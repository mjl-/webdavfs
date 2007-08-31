implement Webdavfs;

include "sys.m";
include "draw.m";
include "arg.m";
include "bufio.m";
	bufio: Bufio;
	Iobuf: import bufio;
include "string.m";
include "styx.m";
	Tmsg, Rmsg: import Styx;
include "styxservers.m";
include "daytime.m";
include "filter.m";
include "tables.m";
include "factotum.m";
include "mhttp.m";
include "xml.m";

sys: Sys;
str: String;
styx: Styx;
styxservers: Styxservers;
daytime: Daytime;
http: Http;
tables: Tables;
xml: Xml;

print, sprint, fprint, fildes: import sys;
Styxserver, Fid, Navigator, Navop: import styxservers;
Parser, Locator, Attributes: import xml;
Table, Strhash: import tables;
Url, Hdrs, Req, Resp: import http;

Estale:		con "stale fid";
Edirnotempty:	con "directory not empty";
Ebadstat:	con "webdav server sent bad stat reponse";
Eexists, Enotdir, Eperm, Enotfound, Ebadfid, Emode, Ebadarg: import Styxservers;

cflag, dflag: int;
baseurl: ref Url;
lastqid := 0;
user: string;
srv: ref Styxserver;
keyspec: string;
qdirtab:	ref Table[array of ref Sys->Dir];	# map qid.path -> directory contents
quptab:		ref Table[string];	# map qid.path -> urlpath
upqtab:		ref Strhash[ref Int];	# map urlpath -> qid.path
OVERWRITE, USERANGE: con iota;
PROPREQ: array of byte;

Int: adt {
	i:	int;
};
nilint: ref Int;

Stat: adt {
	href:   string;
	isdir:  int;
	mtime:  int;
	length: big;
	mode:   int;
	status: ref (string, string, string);

	dir:	fn(s: self Stat, path: big): ref Sys->Dir;
};
zerostat := Stat("", 0, 0, big -1, -1, nil);

Webdavfs: module {
	init:	fn(nil: ref Draw->Context, args: list of string);
};

init(nil: ref Draw->Context, args: list of string)
{
	sys = load Sys Sys->PATH;
	arg := load Arg Arg->PATH;
	bufio = load Bufio Bufio->PATH;
	str = load String String->PATH;
	styx = load Styx Styx->PATH;
	styx->init();
	styxservers = load Styxservers Styxservers->PATH;
	styxservers->init(styx);
	daytime = load Daytime Daytime->PATH;
	xml = load Xml Xml->PATH;
	xml->init(bufio);
	tables = load Tables Tables->PATH;
	http = load Http Http->PATH;
	http->init(bufio);

	# readdir in xml...
	PROPREQ = array of byte "<?xml version=\"1.0\" encoding=\"utf-8\"?><propfind xmlns=\"DAV:\"><prop><getcontentlength xmlns=\"DAV:\"/><getlastmodified xmlns=\"DAV:\"/><executable xmlns=\"http://apache.org/dav/props/\"/><resourcetype xmlns=\"DAV:\"/><checked-in xmlns=\"DAV:\"/><checked-out xmlns=\"DAV:\"/></prop></propfind>";

	arg->init(args);
	arg->setusage(arg->progname()+" [-Dcd] [-k keyspec] url");
	while((c := arg->opt()) != 0)
		case c {
		'D' =>	styxservers->traceset(1);
			http->debug++;
		'c' =>	cflag++;
		'd' =>	dflag++;
		'k' =>	keyspec = arg->earg();
		* =>	arg->usage();
		}
	args = arg->argv();
	if(len args != 1)
		arg->usage();
	err: string;
	(baseurl, err) = Url.unpack(hd args);
	if(err != nil)
		fail(err);
	if(baseurl.query != nil)
		fail("query in url unsupported");
	if(baseurl.path == nil || baseurl.path[len baseurl.path-1] != '/')
		baseurl.path += "/";

	user = readuser();
	nilint = ref Int(-1);;
	qdirtab = qdirtab.new(256, nil);
	quptab = quptab.new(256, nil);
	upqtab = upqtab.new(256, nilint);

	navch := chan of ref Navop;
	spawn navigator(navch);

	nav := Navigator.new(navch);
	msgc: chan of ref Tmsg;
	(msgc, srv) = Styxserver.new(sys->fildes(0), nav, big 0);

done:
	for(;;) {
		gm := <-msgc;
		if(gm == nil)
			break;
		pick m := gm {
		Readerror =>
			warn("read error: "+m.error);
			break done;
		* =>
			dostyx(gm);
		}
	}
	warn("quiting");
}

findurlpath(m: ref Tmsg, fid: int): string
{
	f := srv.getfid(fid);
	if(f == nil) {
		replyerror(m, Ebadfid);
		return nil;
	}
	up := geturlpath(f.path);
	if(up == nil)
		replyerror(m, Estale);
	return up;
}

replyerror(m: ref Tmsg, err: string)
{
	srv.reply(ref Rmsg.Error(m.tag, err));
}

dostyx(gm: ref Tmsg)
{
	pick m := gm {
	Attach =>
		(nil, err) := httpstat(baseurl.path);	# assigns a qid to root path
		if(err != nil)
			return replyerror(m, err);
		srv.default(m);

	Open =>
		if((up := findurlpath(m, m.fid)) == nil)
			return;
		if(m.mode & (Sys->ORCLOSE|Sys->OEXCL))
			return replyerror(m, Emode);
		if(m.mode & Sys->OTRUNC) {
			err := httpput(up, big 0, array[0] of byte, OVERWRITE);
			if(err != nil)
				return replyerror(m, err);
		}
		srv.default(m);

	Create =>
		if((up := findurlpath(m, m.fid)) == nil)
			return;
		(f, mode, d, err) := srv.cancreate(m);
		if(f == nil)
			return replyerror(m, err);
		newup := up+m.name;
		if(m.perm & Sys->DMDIR)
			err = httpmkcol(newup);
		else
			err = httpput(newup, big 0, array[0] of byte, OVERWRITE);
		if(err != nil)
			return replyerror(m, err);
		nqidpath := lastqid++;
		oldqid := getqid(newup);
		if(oldqid >= big 0)
			delqup(oldqid, newup);
		addqup(big nqidpath, newup);
		d.qid.path = big nqidpath;
		d.atime = d.mtime = daytime->now();
		f.open(mode, d.qid);
		srv.reply(ref Rmsg.Create(m.tag, d.qid, srv.iounit()));

	Write =>
		(f, err) := srv.canwrite(m);
		if(f == nil)
			return replyerror(m, err);
		if((up := findurlpath(m, m.fid)) == nil)
			return;
		userange := USERANGE;
		if(m.offset == big 0 && len m.data == 0)
			userange = OVERWRITE;
		err = httpput(up, m.offset, m.data, userange);
		if(err != nil)
			return replyerror(m, err);
		srv.reply(ref Rmsg.Write(m.tag, len m.data));

	Read =>
		(f, err) := srv.canread(m);
		if(f == nil)
			return replyerror(m, err);
		if((up := findurlpath(m, m.fid)) == nil)
			return;
		if(f.qtype & Sys->QTDIR) {
			srv.default(m);
			return;
		}
		(data, derr) := httpget(up, m.offset, m.count);
		if(derr != nil)
			return replyerror(m, derr);
		srv.reply(ref Rmsg.Read(m.tag, data));

	Remove =>
		(f, nil, err) := srv.canremove(m);
		if(f == nil)
			return replyerror(m, err);
		if((up := findurlpath(m, m.fid)) == nil) {
			srv.delfid(f);
			return;
		}

		# webdav removes directories recursively, take care
		if(f.qtype & Sys->QTDIR) {
			(dir, derr) := httpreaddir(up);
			if(derr != nil) {
				srv.delfid(f);
				return replyerror(m, derr);
			}
			if(len dir != 0) {
				srv.delfid(f);
				return replyerror(m, Edirnotempty);
			}
		}
		err = httpdelete(up);
		if(err != nil) {
			srv.delfid(f);
			return replyerror(m, err);
		}
		qdirtab.del(int f.path);
		delqup(f.path, up);
		srv.delfid(f);
		srv.reply(ref Rmsg.Remove(m.tag));

	Wstat =>
		(f, nil, err) := srv.canremove(ref Tmsg.Clunk(m.tag, m.fid));
		if(f == nil)
			return replyerror(m, err);
		if(f.path == big 0)
			return replyerror(m, "cannot change name of root directory");
		if((up := findurlpath(m, m.fid)) == nil)
			return;

		rd := sys->nulldir;
		rd.name = m.stat.name;
		if(!direq(rd, m.stat)) {
			(rrd, rerr) := httpstat(up);
			if(rerr != nil)
				return replyerror(m, err);
			rrd.name = m.stat.name;
			if(!direq(*rrd, m.stat))
				return replyerror(m, "wstat only supported for name");
		}
		newup := walkup(up)+m.stat.name;
		if(f.qtype & Sys->QTDIR)
			newup += "/";
		err = httpmove(up, newup);
		if(err != nil)
			return replyerror(m, err);
		renamequp(up, newup);
		srv.reply(ref Rmsg.Wstat(m.tag));

	Clunk =>
		f := srv.getfid(m.fid);
		if(f != nil)
			qdirtab.del(int f.path);
		srv.default(gm);
		
	* =>	# stat (navigator), flush and clunk
		srv.default(gm);
	}
}

navigator(c: chan of ref Navop)
{
	for(;;) {
		navop := <-c;
		say(sprint("have navop %d", tagof navop));
		up := geturlpath(navop.path);
		if(up == nil) {
			navop.reply <-= (nil, Enotfound);
			continue;
		}

		pick op := navop {
		Stat =>
			say("navop stat");
			op.reply <-= httpstat(up);

		Walk =>
			say("navop walk");
			if(op.name == "..") {
				if(op.path == big 0) {
					op.reply <-= httpstat(baseurl.path);
					continue;
				}
				op.reply <-= httpstat(walkup(up));
				continue;
			}
			if(up[len up-1] != '/') {
				op.reply <-= (nil, Enotdir);
				continue;
			}
			op.reply <-= httpstat(up+op.name);

		Readdir =>
			say("navop readdir");
			if(op.offset == 0)
				qdirtab.del(int op.path);
			dir := qdirtab.find(int op.path);
			if(dir == nil) {
				err: string;
				(dir, err) = httpreaddir(up);
				if(err != nil) {
					op.reply <-= (nil, err);
					continue;
				}
				qdirtab.add(int op.path, dir);
			}

			for(i := 0; i < op.count && op.offset+i < len dir; i++)
				op.reply <-= (dir[i+op.offset], nil);
			op.reply <-= (nil, nil);
		}
	}
}

walkup(s: string): string
{
	if(s[len s-1] == '/')
		s = s[:len s-1];
	(ns, nil) := str->splitstrr(s, "/");
	return ns;
}

httpstat(up: string): (ref Sys->Dir, string)
{
	req := mkreq(Http->PROPFIND, up);
	req.body = PROPREQ;
	req.h.set("Depth", "0");
	req.h.set("Content-Type", "application/xml");
	(fd, resp, err) := httptransact(req);
	if(err != nil)
		return (nil, err);

	(stats, serr) := respstats(fd, resp);
	if(serr != nil)
		return (nil, serr);
	if(len stats != 1)
		return (nil, sprint("too many entries in response, want 1, have %d", len stats));

	if(stats[0].isdir && up[len up-1] != '/')
		up += "/";
	if(!urlpatheq(stats[0].href, up))
		return (nil, Ebadstat);

	qidpath := getqid(up);
	if(qidpath < big 0)
		addqup(qidpath = big lastqid++, up);
	case stats[0].status.t1 {
	* =>
		flushfd(fd);
		return (nil, httperror(resp));
	"200" =>
		return (stats[0].dir(qidpath), nil);
	}

}

respstats(fd: ref Sys->FD, resp: ref Resp): (array of Stat, string)
{
	case resp.st {
	* =>
		flushfd(fd);
		return (nil, httperror(resp));
	"207" =>
		(stats, err) := parsestats(fd);
		if(err != nil)
			return (nil, "parsing response: "+err);
		flushfd(fd);
		return (stats, nil);
	}
}

httpreaddir(up: string): (array of ref Sys->Dir, string)
{
	req := mkreq(Http->PROPFIND, up);
	req.body = PROPREQ;
	req.h.set("Depth", "1");
	req.h.set("Content-Type", "application/xml");
	(fd, resp, err) := httptransact(req);
	if(err != nil)
		return (nil, err);

	(stats, serr) := respstats(fd, resp);
	if(serr != nil)
		return (nil, serr);
	if(len stats == 0)
		return (nil, "no stats in response");

	if(stats[0].isdir && up[len up-1] != '/')
		up += "/";
	if(!urlpatheq(stats[0].href, up))
		return (nil, Ebadstat);

	dirs := array[len stats-1] of ref Sys->Dir;
	for(i := 1; i < len stats; i++)
		case stats[i].status.t1 {
		"404" =>		return (nil, Enotfound);
		"401" or "403" =>	return (nil, Eperm);
		* =>			return (nil, sprint("%s (%s)", stats[i].status.t1, stats[i].status.t0));
		"200" =>
			if(!urlpatheq(walkup(stats[i].href), up))
				return (nil, Ebadstat);

			dirs[i-1] = stats[i].dir(big -1);
			newup := up+dirs[i-1].name;
			qidpath := getqid(newup);
			if(qidpath < big 0)
				addqup(qidpath = big lastqid++, newup);
			dirs[i-1].qid.path = qidpath;
		}
	return (dirs, nil);
}

urlpatheq(href, up: string): int
{
	say(sprint("EQ href=%q up=%q", href, up));
	if(str->prefix("http://", href) || str->prefix("https://", href)) {
		(url, err) := Url.unpack(href);
		if(err != nil)
			return 0;
		say(sprint("EQ TEST url.path=%q up=%q url.ssl=%d url.host=%q url.port=%q baseurl.port=%q", url.path, up, url.usessl, url.host, url.port, baseurl.port));
		urlpath := url.path;
		if(urlpath[len urlpath-1] != '/' && up[len up-1] == '/')
			up = up[:len up-1];
		return url.path == up
			&& baseurl.usessl == url.usessl
			&& baseurl.host == url.host; # xxx lighttpd webdav is broken: && baseurl.port == url.port;
	}
	if(href[len href-1] != '/' && up[len up-1] == '/')
		up = up[:len up-1];
	return href == up;
}

httperror(resp: ref Resp): string
{
	case resp.st {
	"403" or "401" =>	return Eperm;
	"404" =>		return Enotfound;
	* =>			return sprint("%s (%s)", resp.stmsg, resp.st);
	}
}

httpmove(up, newup: string): string
{
	req := mkreq(Http->MOVE, up);
	req.h.set("Overwrite", "F");
	newurl := ref *baseurl;
	newurl.path = newup;
	newurlstr := newurl.pack();
	if(newurl.host == "localhost")	# xxx lighttpd doesn't know its port...
		newurlstr = "http://localhost"+newurl.path;
	req.h.set("Destination", newurlstr);
	(fd, resp, err) := httptransact(req);
	if(err != nil)
		return err;
	flushfd(fd);

	case resp.st{
	"201" or "204" =>	return nil;
	* =>	return httperror(resp);
	}
}

httpdelete(up: string): string
{
	req := mkreq(Http->DELETE, up);
	(fd, resp, err) := httptransact(req);
	if(err != nil)
		return err;
	flushfd(fd);

	case resp.st {
	"200" or "202" or "204" =>
		return nil;
	* =>	return httperror(resp);
	}
}

httpput(up: string, off: big, d: array of byte, userange: int): string
{
	req := mkreq(Http->PUT, up);
	req.body = d;
	if(userange)
		req.h.set("Content-Range", sprint("bytes %bd-%bd/*", off, off+big len d-big 1));
	(fd, resp, err) := httptransact(req);
	if(err != nil)
		return err;
	flushfd(fd);

	case resp.st {
	"200" or "201" or "204" =>
		return nil;
	* =>	return httperror(resp);
	}
}

httpmkcol(up: string): string
{
	req := mkreq(Http->MKCOL, up);
	(fd, resp, err) := httptransact(req);
	if(err != nil)
		return err;
	flushfd(fd);

	case resp.st {
	"405" =>	return Eexists;
	* =>		return httperror(resp);
	"201" =>	return nil;
	}
}

httpget(up: string, off: big, count: int): (array of byte, string)
{
	req := mkreq(Http->GET, up);
	req.h.set("Range", sprint("bytes=%bd-%bd", off, off+big (count-1)));
	(fd, resp, err) := httptransact(req);
	if(err != nil)
		return (nil, err);

	case resp.st {
	* =>
		flushfd(fd);
		return (nil, httperror(resp));
	"200" or "206" =>
		return readfd(fd);
	"416" =>
		flushfd(fd);
		return (array[0] of byte, nil);
	}
}

parsestats(fd: ref Sys->FD): (array of Stat, string)
{
	b := bufio->fopen(fd, Sys->OREAD);
	if(b == nil)
		return (nil, sprint("bufio aopen: %r"));

	(p, err) := xml->fopen(b, "stats", nil, nil);
	if(err != nil)
		return (nil, err);

	hier := array[] of {
		("",			"multistatus"::nil),
		("multistatus",		"response"::nil),
		("response",		"href"::"propstat"::nil),
		("propstat",		"prop"::"status"::nil),
		("prop",		"resourcetype"::"getlastmodified"::"getcontentlength"::"mode"::nil),
		("resourcetype",	"collection"::nil),
	};
	path: list of string;

	stats := array[0] of Stat;
	stat := zerostat;
	for(;;) {
		item := p.next();
		if(item == nil) {
			if(path == nil)
				break;
			case hd path {
			"collection" =>
				stat.isdir = 1;
			"response" =>
				if(stat.status == nil)
					return (nil, "missing http status");
				if(stat.status.t1 == "200" &&
					(stat.length == zerostat.length
					|| stat.href == zerostat.href
					|| stat.status == zerostat.status))
					return (nil, "missing stat info");
				nstats := array[len stats+1] of Stat;
				nstats[:] = stats;
				nstats[len stats] = stat;
				stats = nstats;
				stat = zerostat;
			}
			#say("going up");
			p.up();
			path = tl path;
			continue;
		}
		pick it := item {
		Tag =>
			(nil, name) := str->splitstrl(it.name, ":");
			if(name != nil && name[0] == ':')
				name = name[1:];

			elem := "";
			if(len path > 0)
				elem = hd path;
		search:
			for(i := 0; i < len hier; i++)
				if(elem == hier[i].t0)
					for(l := hier[i].t1; l != nil; l = tl l)
						if(name == hd l) {
							path = name::path;
							p.down();
							break search;
						}
		Text =>
			if(path == nil)
				continue;
			case hd path {
			"href" =>
				stat.href = http->decode(it.ch);	# xxx should probably decode html/xml entities as well
			"status" =>
				l := it.ch;
				vers, code, msg: string;
				(vers, l) = str->splitstrl(l, " ");
				if(l != nil) l = l[1:];
				(code, l) = str->splitstrl(l, " ");
				if(l != nil) l = l[1:];
				msg = l;
				if(vers == nil || code == nil || msg == nil)
					return (nil, "bad status message");
				stat.status = ref (vers, code, msg);
			"getlastmodified" =>
				tm := daytime->string2tm(it.ch);
				if(tm == nil)
					return (nil, sprint("bad time format: %q", it.ch));
				stat.mtime = daytime->tm2epoch(tm);
			"getcontentlength" =>
				stat.length = big it.ch;
			"mode" =>
				(mode, rem) := str->toint(it.ch, 8);
				if(rem != nil)
					return (nil, "bad mode");
				stat.mode = mode;
			* =>
				; #say(sprint("text: %q (%d %d)", it.ch, it.ws1, it.ws2));
			}
		Error =>
			return (nil, "parsing xml: "+it.msg);
		* =>
			#say("other type");
		}
	}
	#say("done");
	return (stats, nil);
}

mkurl(up: string): ref Url
{
	return ref Url(baseurl.usessl, baseurl.scheme, baseurl.host, baseurl.port, up, nil);
}

mkreq(method: int, up: string): ref Req
{
	return ref Req(method, mkurl(up), Http->HTTP_11, Hdrs.new(nil), nil, nil);
}

Stat.dir(s: self Stat, path: big): ref Sys->Dir
{
	d := sys->zerodir;
	d.name = s.href;
	if(d.name[len d.name-1] == '/')
		d.name = d.name[:len d.name-1];
	(nil, d.name) = str->splitstrr(d.name, "/");
	d.uid = d.gid = d.muid = user;
	d.qid.path = path;
	d.qid.vers = 0;		# xxx increase version number on writes?
	d.qid.qtype = Sys->QTFILE;
	if(s.isdir)
		d.qid.qtype = Sys->QTDIR;
	d.mode = s.mode;
	if(s.mode < 0) {
		d.mode = 8r640;
		if(s.isdir)
			d.mode = 8r750;
	}
	if(s.isdir)
		d.mode |= Sys->DMDIR;
	d.atime = d.mtime = s.mtime;
	d.length = s.length;
	if(s.isdir)
		d.length = big 0;
	d.dtype = d.dev = 0;
	return ref d;
}

getqid(up: string): big
{
	return big upqtab.find(up).i;
}

geturlpath(qid: big): string
{
	return quptab.find(int qid);
}

renamequp(up, newup: string)
{
	isdir := up[len up-1] == '/';

	# horrible, need interface to get all items in tables
	newtab := upqtab;
	newtab = newtab.new(len upqtab.items, upqtab.nilval);
	for(i := 0; i < len upqtab.items; i++) {
		for(l := upqtab.items[i]; l != nil; l = tl l) {
			(fullup, qint) := hd l;
			if((isdir && len fullup >= len up && fullup[:len up] == up) || up == fullup)
				newtab.add(newup+fullup[len up:], qint);
			else
				newtab.add(fullup, qint);
		}
	}
	upqtab = newtab;

	for(i = 0; i < len quptab.items; i++) {
		l := r := quptab.items[i];
		for(; l != nil; l = tl l) {
			(qid, fullup) := hd l;
			if((isdir && len fullup >= len up && fullup[:len up] == up) || up == fullup)
				r = (qid, newup+fullup[len up:])::r;
			else
				r = hd l::r;
		}
		quptab.items[i] = r;
	}
}

delqup(qid: big, up: string)
{
	quptab.del(int qid);
	upqtab.del(up);
}

addqup(qid: big, up: string)
{
	quptab.add(int qid, up);
	upqtab.add(up, ref Int(int qid));
}

devnullfd: ref Sys->FD;
hfd: ref Sys->FD;
hb: ref Iobuf;

flushfd(fd: ref Sys->FD): string
{
	if(fd == nil)
		return nil;
	if(devnullfd == nil) {
		devnullfd = sys->open("/dev/null", Sys->OWRITE);
		if(devnullfd == nil) {
			hfd = nil;
			return sprint("opening /dev/null: %r");
		}
	}
	if(sys->stream(fd, devnullfd, Sys->ATOMICIO) < 0) {
		hfd = nil;
		return sprint("flushing http response body to /dev/null: %r");
	}
	return nil;
}

authhdr: ref (string, string);
authtried := 0;

httptransact(req: ref Req): (ref Sys->FD, ref Resp, string)
{
	err: string;
	resp: ref Resp;
	reusing := 1;
	for(i := 0; i < 10; i++) {
		if(authhdr != nil)
			req.h.set(authhdr.t0, authhdr.t1);
		if(cflag)
			req.h.set("Connection", "close");
		if(cflag || !reusing || !http->isidempotent(req.method) || hfd == nil || hb == nil) {
			(hfd, err) = req.dial();
			if(err != nil)
				return (nil, nil, err);
			hb = bufio->fopen(hfd, Sys->OREAD);
			if(hb == nil)
				return (nil, nil, sprint("bufio fopen: %r"));
			reusing = 0;
		} else
			reusing = 1;

		err = req.write(hfd);
		if(err != nil && reusing) {
			reusing = 0;
			continue;
		}
		if(err != nil)
			return (nil, nil, err);

		(resp, err) = Resp.read(hb);
		if(err != nil && reusing) {
			reusing = 0;
			continue;
		}
		if(err != nil)
			return (nil, nil, err);
		if(int resp.st == 401 && !authtried && ((nil, wwwauth) := resp.h.find("WWW-Authenticate")).t0) {
			if(str->prefix("Basic", wwwauth)) {
				f := load Factotum Factotum->PATH;
				f->init();
				(huser, hpass) := f->getuserpasswd(sprint("proto=pass server=%q service=httpbasic %s", baseurl.pack(), keyspec));
				authtried = 1;
				if(huser != nil || hpass != nil) {
					authhdr = ref http->basicauth(huser, hpass);
					continue;
				}
			} else {
				(bfd, berr) := resp.body(hb);
				if(berr != nil)
					return (nil, nil, "reading body for redirect: "+berr);
				if((err = flushfd(bfd)) != nil)
					return (nil, nil, sprint("flushing http response body to /dev/null: %r"));
				return (nil, nil, "unsupported http auth type: "+wwwauth);
			}
		}
		if(req.method == Http->PROPFIND)
			case int resp.st {
			301 or 302 or 303 or 307 =>
				if(resp.hasbody(req.method)) {
					(bfd, berr) := resp.body(hb);
					if(berr != nil)
						return (nil, nil, "reading body for redirect: "+berr);
					if((err = flushfd(bfd)) != nil)
						return (nil, nil, sprint("flushing http response body to /dev/null: %r"));
				}
				(has, ustr) := resp.h.find("Location");
				if(!has)
					return (nil, nil, sprint("missing Location in redirect"));
				(newurl, uerr) := Url.unpack(ustr);
				if(uerr != nil)
					return (nil, nil, "new url: "+uerr);
				# xxx verify newurl doesn't point to other scheme/host/port/basepath
				req.url = newurl;
				if(resp.h.has("Connection", "close")) {
					hfd = nil;
					hb = nil;
				}
				continue;
			}
		break;
	}

	bfd: ref Sys->FD;
	if(resp.hasbody(req.method)) {
		say("calling body");
		(bfd, err) = resp.body(hb);
		if(err != nil)
			return (nil, nil, err);
		say("body returned");
	}
	if(resp.h.has("Connection", "close")) {
		hfd = nil;
		hb = nil;
	}
	return (bfd, resp, nil);
}

direq(d1, d2: Sys->Dir): int
{
	d1.qid.qtype = (d1.qid.qtype<<24)>>24;
	d2.qid.qtype = (d2.qid.qtype<<24)>>24;
	d1.dtype = (d1.dtype<<16)>>16;
	d2.dtype = (d2.dtype<<16)>>16;
	say("DIREQ:");
	say(sprint("\tname: %q %q", d1.name, d2.name));
	say(sprint("\tuid: %q %q", d1.uid, d2.uid));
	say(sprint("\tgid: %q %q", d1.gid, d2.gid));
	say(sprint("\tmuid: %q %q", d1.muid, d2.muid));
	say(sprint("\tqid.path: %bd %bd", d1.qid.path, d2.qid.path));
	say(sprint("\tqid.vers: %d %d", d1.qid.vers, d2.qid.vers));
	say(sprint("\tqid.qtype: %d %d", d1.qid.qtype, d2.qid.qtype));
	say(sprint("\tmode: %d %d", d1.mode, d2.mode));
	say(sprint("\tatime: %d %d", d1.atime, d2.atime));
	say(sprint("\tmtime: %d %d", d1.mtime, d2.mtime));
	say(sprint("\tlength: %bd %bd", d1.length, d2.length));
	say(sprint("\tdtype: %d %d", d1.dtype, d2.dtype));
	say(sprint("\tdev: %d %d", d1.dev, d2.dev));
	return d1.name == d2.name &&
		d1.uid == d2.uid &&
		d1.gid == d2.gid &&
		d1.muid == d2.muid &&
		d1.qid.path == d2.qid.path &&
		d1.qid.vers == d2.qid.vers &&
		d1.qid.qtype == d2.qid.qtype &&
		d1.mode == d2.mode &&
		d1.atime == d2.atime &&
		d1.mtime == d2.mtime &&
		d1.length == d2.length &&
		d1.dtype == d2.dtype &&
		d1.dev == d2.dev;
}

readfd(fd: ref Sys->FD): (array of byte, string)
{
	d := array[0] of byte;
	for(;;) {
		n := sys->read(fd, buf := array[8*1024] of byte, len buf);
		if(n < 0)
			return (nil, sprint("%r"));
		if(n == 0)
			break;
		nd := array[len d+n] of byte;
		nd[:] = d;
		nd[len d:] = buf[:n];
		d = nd;
	}
	return (d, nil);
}

readuser(): string
{
	fd := sys->open("/dev/user", Sys->OREAD);
	if(fd == nil || (n := sys->readn(fd, d := array[128] of byte, len d)) <= 0)
		return "none";
	return string d[:n];
}

warn(s: string)
{
	fprint(fildes(2), "%s\n", s);
}

say(s: string)
{
	if(dflag)
		fprint(fildes(2), "%s\n", s);
}

fail(s: string)
{
	fprint(fildes(2), "%s\n", s);
	raise "fail:"+s;
}
