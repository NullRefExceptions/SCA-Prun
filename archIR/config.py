import pathlib


BUILD_DIR = "/home/xd/builddir"
MAKECONFIG = str(pathlib.Path(__file__).parent.resolve())+"/makepkg.conf"
BC_DIR = "/home/xd/archIR/bc-results"
ROOT_DIR = "/home/xd/archIR"

buildSet = [
{"name": "zlib", "desc": "zlib replacement with optimizations for next generation systems", "rdep": 483},
{"name": "openssl", "desc": "The Open Source toolkit for Secure Sockets Layer and Transport Layer Security", "rdep": 407},
{"name": "libx11", "desc": "X11 client-side library", "rdep": 321},
{"name": "curl", "desc": "A filesystem for acessing FTP hosts based on FUSE and libcurl.", "rdep": 234},
{"name": "libxml2", "desc": "XML C parser and toolkit", "rdep": 221},
{"name": "libpng", "desc": "A collection of routines used to create PNG format graphics files", "rdep": 213},
{"name": "libjpeg-turbo", "desc": "JPEG image codec with accelerated baseline compression and decompression", "rdep": 197},
{"name": "cairo", "desc": "2D graphics library with support for multiple output devices", "rdep": 186},
{"name": "zstd", "desc": "Zstandard - Fast real-time compression algorithm", "rdep": 135},
{"name": "pango", "desc": "A library for layout and rendering of text", "rdep": 122},
{"name": "bzip2", "desc": "A high-quality data compression program", "rdep": 111},
{"name": "gnutls", "desc": "A library which provides a secure layer over a reliable transport layer", "rdep": 107},
{"name": "icu", "desc": "International Components for Unicode library", "rdep": 99},
{"name": "libsndfile", "desc": "A C library for reading and writing files containing sampled audio data", "rdep": 96},
{"name": "ffmpeg", "desc": "Complete solution to record, convert and stream audio and video", "rdep": 94},
{"name": "librsvg", "desc": "SVG rendering library", "rdep": 77},
{"name": "pcre2", "desc": "A library that implements Perl 5-style regular expressions. 2nd version", "rdep": 71},
{"name": "libtiff", "desc": "Library for manipulation of TIFF images", "rdep": 70},
{"name": "libarchive", "desc": "Multi-format archive and compression library", "rdep": 63},
{"name": "libxkbcommon", "desc": "Keymap handling library for toolkits and window systems", "rdep": 63},
{"name": "libpcap", "desc": "A system-independent interface for user-level packet capture", "rdep": 59},
{"name": "libseccomp", "desc": "Enhanced seccomp library", "rdep": 53},
{"name": "libxslt", "desc": "XML stylesheet transformation library", "rdep": 53},
{"name": "flac", "desc": "Free Lossless Audio Codec", "rdep": 44},
{"name": "libevent", "desc": "Event notification library", "rdep": 49},
{"name": "libgcrypt", "desc": "General purpose cryptographic library based on the code from GnuPG", "rdep": 48},
{"name": "libuv", "desc": "Multi-platform support library with a focus on asynchronous I/O", "rdep": 38},
{"name": "jansson", "desc": "C library for encoding, decoding and manipulating JSON data", "rdep": 38},
{"name": "libffi", "desc": "Portable foreign function interface library", "rdep": 36},
{"name": "json-c", "desc": "A JSON implementation in C", "rdep": 34},
{"name": "nettle", "desc": "A low-level cryptographic library", "rdep": 33},
{"name": "libtool", "desc": "A generic library support script", "rdep": 32},
{"name": "taglib", "desc": "A Library for reading and editing the meta-data of several popular audio formats", "rdep": 31},
{"name": "libgit2", "desc": "A linkable library for Git", "rdep": 29},
{"name": "c-ares", "desc": "A C library for asynchronous DNS requests", "rdep": 27},
{"name": "acl", "desc": "Access control list utilities, libraries and headers", "rdep": 27},
{"name": "libexif", "desc": "Library to parse an EXIF file and read the data from those tags", "rdep": 26},
{"name": "fribidi", "desc": "A Free Implementation of the Unicode Bidirectional Algorithm", "rdep": 26},
{"name": "libzip", "desc": "C library for reading, creating, and modifying zip archives", "rdep": 25},
{"name": "libyaml", "desc": "YAML 1.1 library", "rdep": 22},
{"name": "libidn", "desc": "Implementation of the Stringprep, Punycode and IDNA specifications", "rdep": 22},
{"name": "libslirp", "desc": "General purpose TCP-IP emulator", "rdep": 22},
{"name": "openexr", "desc": "A high dynamic-range image file format library", "rdep": 21},
{"name": "libinput", "desc": "Input device management and event handling library", "rdep": 20},
{"name": "libidn2", "desc": "Free software implementation of IDNA2008, Punycode and TR46", "rdep": 19},
{"name": "exiv2", "desc": "Exif, Iptc and XMP metadata manipulation library and tools", "rdep": 18},
{"name": "libbsd", "desc": "Provides useful functions commonly found on BSD systems like strlcpy()", "rdep": 16},
{"name": "libvpx", "desc": "VP8 and VP9 codec", "rdep": 15},
{"name": "libssh", "desc": "Library for accessing ssh client services through C libraries", "rdep": 14},
{"name": "gdal", "desc": "A translator library for raster and vector geospatial data formats", "rdep": 14},
{"name": "libraw", "desc": "A library for reading RAW files obtained from digital photo cameras (CRW/CR2, NEF, RAF, DNG, and others)", "rdep": 13},
{"name": "libass", "desc": "A portable library for SSA/ASS subtitles rendering", "rdep": 13},
{"name": "libssh2", "desc": "A library implementing the SSH2 protocol as defined by Internet Drafts", "rdep": 13},
{"name": "libcdio", "desc": "GNU Compact Disc Input and Control Library", "rdep": 11},
{"name": "libheif", "desc": "An HEIF and AVIF file format decoder and encoder", "rdep": 10},
{"name": "libgphoto2", "desc": "Digital camera access library", "rdep": 9},
{"name": "sdl_ttf", "desc": "A library that allows you to use TrueType fonts in your SDL applications", "rdep": 9},
{"name": "libmicrohttpd", "desc": "a small C library that is supposed to make it easy to run an HTTP server as part of another application.", "rdep": 9},
{"name": "libmaxminddb", "desc": "MaxMindDB GeoIP2 database library", "rdep": 9},
{"name": "faad2", "desc": "Freeware Advanced Audio (AAC) Decoder", "rdep": 9},
{"name": "libavif", "desc": "Library for encoding and decoding .avif files", "rdep": 7},
{"name": "hiredis", "desc": "Minimalistic C client library for Redis", "rdep": 7},
{"name": "wavpack", "desc": "Audio compression format with lossless, lossy and hybrid compression modes", "rdep": 7},
{"name": "libplist", "desc": "Library to handle Apple Property List files", "rdep": 6},
{"name": "soundtouch", "desc": "An audio processing library", "rdep": 6},
{"name": "libtasn1", "desc": "The ASN.1 library used in GNUTLS", "rdep": 6},
{"name": "libmspack", "desc": "A library for Microsoft compression formats", "rdep": 6},
{"name": "exo", "desc": "Application library for the Xfce desktop environment", "rdep": 5},
{"name": "zziplib", "desc": "A lightweight library that offers the ability to easily extract data from files archived in a single zip file", "rdep": 5},
{"name": "glib-networking", "desc": "Network extensions for GLib", "rdep": 5},
{"name": "oniguruma", "desc": "a regular expressions library", "rdep": 5},
{"name": "seatd", "desc": "A minimal seat management daemon, and a universal seat management library", "rdep": 4},
{"name": "libofx", "desc": "API for the OFX banking standard", "rdep": 4},
{"name": "libcaca", "desc": "Color ASCII art library", "rdep": 4},
{"name": "iniparser", "desc": "A free stand-alone ini file parsing library written in portable ANSI C", "rdep": 4},
{"name": "shapelib", "desc": "Simple C API for reading and writing ESRI Shapefiles", "rdep": 4},
{"name": "libgdata", "desc": "GLib-based library for accessing online service APIs using the GData protocol", "rdep": 4},
{"name": "gnome-autoar", "desc": "Automatic archives creating and extracting library", "rdep": 4},
{"name": "libvncserver", "desc": "Cross-platform C libraries that allow you to easily implement VNC server or client functionality", "rdep": 4},
{"name": "libsass", "desc": "C implementation of Sass CSS preprocessor (library)", "rdep": 3},
{"name": "libebml", "desc": "Extensible Binary Meta Language library", "rdep": 3},
{"name": "audiofile", "desc": "Silicon Graphics Audio File Library", "rdep": 3},
{"name": "crun", "desc": "A fast and lightweight fully featured OCI runtime and C library for running containers", "rdep": 3},
{"name": "cracklib", "desc": "Password Checking Library", "rdep": 3},
{"name": "libmatroska", "desc": "Matroska library", "rdep": 3},
{"name": "libsrtp", "desc": "Library for SRTP (Secure Realtime Transport Protocol)", "rdep": 3},
{"name": "libgxps", "desc": "XPS Documents library", "rdep": 3},
{"name": "mongo-c-driver", "desc": "A client library written in C for MongoDB", "rdep": 3},
{"name": "jbig2dec", "desc": "Decoder implementation of the JBIG2 image compression format", "rdep": 3},
{"name": "libde265", "desc": "Open h.265 video codec implementation", "rdep": 2},
{"name": "liblouis", "desc": "Braille translator and back-translator library", "rdep": 2},
{"name": "libspiro", "desc": "Library that simplifies the drawing of beautiful curves", "rdep": 2},
{"name": "libtpms", "desc": "Library providing a software emulation of a Trusted Platform Module (TPM 1.2 and TPM 2.0)", "rdep": 2},
{"name": "wildmidi", "desc": "Simple software MIDI player which has a core softsynth library", "rdep": 2},
{"name": "cmark-gfm", "desc": "GitHub's fork of cmark, a CommonMark parsing and rendering library and program in C", "rdep": 2},
{"name": "gcab", "desc": "A GObject library to create cabinet files", "rdep": 2},
{"name": "libsixel", "desc": "Provides a codec for DEC SIXEL graphics and some converter programs", "rdep": 2},
{"name": "virglrenderer", "desc": "A virtual 3D GPU library, that allows the guest operating system to use the host GPU to accelerate 3D rendering", "rdep": 2},
{"name": "cjson", "desc": "Ultralightweight JSON parser in ANSI C", "rdep": 2},
{"name": "libetpan", "desc": "A portable middleware for email access", "rdep": 1},
{"name": "libvips", "desc": "A fast image processing library with low memory needs", "rdep": 1},
{"name": "stb", "desc": "Single-file public domain (or MIT licensed) libraries for C/C++", "rdep": 1},
{"name": "libsolv", "desc": "Library for solving packages and reading repositories", "rdep": 1},
{"name": "libmysofa", "desc": "C library to read HRTFs if they are stored in the AES69-2015 SOFA format", "rdep": 1},
{"name": "swtpm", "desc": "Libtpms-based TPM emulator with socket, character device, and Linux CUSE interface", "rdep": 1},
{"name": "libusbmuxd", "desc": "Client library to multiplex connections from and to iOS devices", "rdep": 1},
{"name": "uriparser", "desc": "uriparser is a strictly RFC 3986 compliant URI parsing library. uriparser is cross-platform, fast, supports Unicode", "rdep": 1},
{"name": "opensc", "desc": "Tools and libraries for smart cards", "rdep": 1},
{"name": "fdkaac", "desc": "Command line encoder frontend for libfdk-aac", "rdep": 1},
{"name": "poco", "desc": "C++ class libraries for network-centric, portable applications, complete edition with debug libraries", "rdep": 1},
{"name": "libdwarf", "desc": "A library for handling DWARF Debugging Information Format", "rdep": 1},
{"name": "cgal", "desc": "Computational Geometry Algorithms Library", "rdep": 1},
{"name": "libndp", "desc": "Library for Neighbor Discovery Protocol", "rdep": 1},
{"name": "wolfssl", "desc": "Lightweight, portable, C-language-based SSL/TLS library", "rdep": 1},
{"name": "libtorrent", "desc": "BitTorrent library with a focus on high performance and good code", "rdep": 1},
{"name": "tcpreplay", "desc": "Gives the ability to replay previously captured traffic in a libpcap format", "rdep": 1},
{"name": "libgadu", "desc": "Client-side library for the Gadu-Gadu protocol", "rdep": 1},
{"name": "libextractor", "desc": "A library used to extract meta-data from files of arbitrary type", "rdep": 1},
{"name": "libtomcrypt", "desc": "A fairly comprehensive, modular and portable cryptographic toolkit", "rdep": 1}
]

#由于依赖装不上等原因无法完成编译,较容易修复
installDepErrorSet = [
{"name": "ncurses", "desc": "System V Release 4.0 curses emulation library", "rdep": 188},
{"name": "fmt", "desc": "Open-source formatting library for C++", "rdep": 41},
{"name": "poppler", "desc": "PDF rendering library based on xpdf 3.0", "rdep": 16},
{"name": "libvirt", "desc": "API for controlling virtualization engines (openvz,kvm,qemu,virtualbox,xen,etc)", "rdep": 8},
{"name": "dpdk", "desc": "A set of libraries and drivers for fast packet processing", "rdep": 1}
]

#由于llvm无法与gcc兼任而无法完成编译,较难修复
buildErrorSet =  [
{"name": "glibc", "desc": "GNU C Library", "rdep": 2059},
{"name": "imagemagick", "desc": "An image viewing/manipulation program", "rdep": 31},
{"name": "libsoup", "desc": "HTTP client/server library for GNOME", "rdep": 29},
{"name": "libjxl", "desc": "JPEG XL image format reference implementation", "rdep": 13},
{"name": "jasper", "desc": "Software-based implementation of the codec specified in the emerging JPEG-2000 Part-1 standard", "rdep": 10},
{"name": "libgsf", "desc": "Extensible I/O abstraction library for dealing with structured file formats", "rdep": 6},
{"name": "raptor", "desc": "A C library that parses RDF/XML/N-Triples into RDF triples", "rdep": 6},
{"name": "libimobiledevice", "desc": "Library to communicate with services on iOS devices using native protocols", "rdep": 5},
{"name": "mbedtls", "desc": "An open source, portable, easy to use, readable and flexible TLS library", "rdep": 4},
{"name": "ldns", "desc": "Fast DNS library supporting recent RFCs", "rdep": 3},
{"name": "gpsd", "desc": "GPS daemon and library to support USB/serial GPS devices", "rdep": 3},
{"name": "rhonabwy", "desc": "JWK, JWKS, JWS, JWE and JWT C library", "rdep": 2},
{"name": "botan", "desc": "Crypto library written in C++", "rdep": 2},
{"name": "libcomps", "desc": "Comps XML file manipulation library", "rdep": 1},
{"name": "libnbd", "desc": "NBD client library in userspace", "rdep": 1},
{"name": "libcroco", "desc": "A CSS parsing library", "rdep": 1},
{"name": "librepo", "desc": "Repodata downloading library", "rdep": 1},
{"name": "libqb", "desc": "Library for providing high performance, reusable features for client-server architecture", "rdep": 1},
{"name": "libinfinity", "desc": "A library to build collaborative text editors. Includes the infinoted server", "rdep": 1}
]

#too big
skipSet = [
{"name": "tensorflow", "desc": "Library for computation using data flow graphs for scalable machine learning", "rdep": 1},
{"name": "opencv", "desc": "Open Source Computer Vision Library", "rdep": 22}, 
{"name": "libguestfs", "desc": "Access and modify virtual machine disk images", "rdep": 1}
]

#not lib
exculdeSet = [
{"name": "feh", "desc": "Fast and light imlib2-based image viewer", "rdep": 1},
{"name": "qbittorrent", "desc": "An advanced BitTorrent client programmed in C++, based on Qt toolkit and libtorrent-rasterbar", "rdep": 1},
{"name": "aubio", "desc": "A tool for extracting annotations from audio signals", "rdep": 9},
{"name": "picocom", "desc": "Minimal dumb-terminal emulation program, very much like minicom", "rdep": 1},
{"name": "shotcut", "desc": "Cross-platform Qt based Video Editor", "rdep": 1},
{"name": "jq", "desc": "Command-line JSON processor", "rdep": 5},
{"name": "unrealircd", "desc": "Open Source IRC Server", "rdep": 1},
{"name": "nasm", "desc": "80x86 assembler designed for portability and modularity", "rdep": 1},
{"name": "memcached", "desc": "Distributed memory object caching system", "rdep": 1},
{"name": "mpv", "desc": "a free, open source, and cross-platform media player", "rdep": 13},
{"name": "lrzip", "desc": "Multi-threaded compression with rzip/lzma, lzo, and zpaq", "rdep": 2},
{"name": "gnome-settings-daemon", "desc": "GNOME Settings Daemon", "rdep": 9},
{"name": "ntp", "desc": "Network Time Protocol reference implementation", "rdep": 1},
{"name": "avahi", "desc": "Service Discovery for Linux using mDNS/DNS-SD (compatible with Bonjour)", "rdep": 41},
{"name": "eog", "desc": "Eye of Gnome: An image viewing and cataloging program", "rdep": 1},
{"name": "http-parser", "desc": "Parser for HTTP Request/Response written in C", "rdep": 6},
{"name": "t1utils", "desc": "Utilities for manupulating Adobe Type 1 font software", "rdep": 1},
{"name": "gst-plugins-base", "desc": "Multimedia graph framework - base plugins", "rdep": 43},
{"name": "fontforge", "desc": "Outline and bitmap font editor", "rdep": 1},
{"name": "gnome-shell", "desc": "Next generation desktop shell", "rdep": 10},
{"name": "tigervnc", "desc": "Suite of VNC servers and clients. Based on the VNC 4 branch of TightVNC.", "rdep": 1},
{"name": "polkit", "desc": "Application development toolkit for controlling system-wide privileges", "rdep": 56},
{"name": "epiphany", "desc": "A GNOME web browser based on the WebKit rendering engine", "rdep": 1},
{"name": "minetest", "desc": "Multiplayer infinite-world block sandbox game", "rdep": 1},
{"name": "ppp", "desc": "Utility to monitor pppd connections", "rdep": 10},
{"name": "shim", "desc": "EFI preloader (unsigned EFI binaries)", "rdep": 1},
{"name": "neovim", "desc": "Fork of Vim aiming to improve user experience, plugins, and GUIs", "rdep": 35},
{"name": "runc", "desc": "CLI tool for managing OCI compliant containers", "rdep": 4},
{"name": "icoutils", "desc": "Extracts and converts images in MS Windows(R) icon and cursor files.", "rdep": 1},
{"name": "harfbuzz", "desc": "OpenType text shaping engine", "rdep": 48},
{"name": "godot", "desc": "Advanced cross-platform 2D and 3D game engine", "rdep": 1},
{"name": "gnuplot", "desc": "Plotting package which outputs to X11, PostScript, PNG, GIF, and others", "rdep": 5},
{"name": "pngquant", "desc": "Command-line utility to quantize PNGs down to 8-bit paletted PNGs", "rdep": 1},
{"name": "bwm-ng", "desc": "A small and simple console-based live bandwidth monitor", "rdep": 1},
{"name": "gst-plugins-ugly", "desc": "Multimedia graph framework - ugly plugins", "rdep": 5},
{"name": "kitty", "desc": "A modern, hackable, featureful, OpenGL-based terminal emulator", "rdep": 1},
{"name": "gstreamer", "desc": "Multimedia graph framework - core", "rdep": 40},
{"name": "gnupg", "desc": "Smart-card daemon to enable the use of PKCS#11 tokens with GnuPG", "rdep": 20},
{"name": "tang", "desc": "Server for binding data to network presence", "rdep": 1},
{"name": "samba", "desc": "SMB Fileserver and AD Domain server", "rdep": 4},
{"name": "gegl", "desc": "Graph based image processing framework", "rdep": 4},
{"name": "tcpflow", "desc": "Captures data transmitted as part of TCP connections then stores the data conveniently", "rdep": 1},
{"name": "mujs", "desc": "An embeddable Javascript interpreter in C", "rdep": 1},
{"name": "ocaml", "desc": "A functional language with OO extensions", "rdep": 32},
{"name": "iperf", "desc": "A tool to measure maximum TCP bandwidth", "rdep": 1},
{"name": "coturn", "desc": "Open-source implementation of TURN and STUN server", "rdep": 1},
{"name": "gnome-session", "desc": "The GNOME Session Handler", "rdep": 6},
{"name": "e2fsprogs", "desc": "Ext2/3/4 filesystem utilities", "rdep": 16},
{"name": "mosh", "desc": "Mobile shell, surviving disconnects with local echo and line editing", "rdep": 1},
{"name": "tmux", "desc": "Terminal multiplexer", "rdep": 2},
{"name": "radvd", "desc": "IPv6 Router Advertisement Daemon", "rdep": 1},
{"name": "network-manager-applet", "desc": "Applet for managing network connections", "rdep": 1},
{"name": "tcpdump", "desc": "Powerful command-line packet analyzer", "rdep": 2},
{"name": "chrony", "desc": "Lightweight NTP client and server", "rdep": 1},
{"name": "openscad", "desc": "The programmers solid 3D CAD modeller", "rdep": 1},
{"name": "bpf", "desc": "BPF tools", "rdep": 1},
{"name": "cryptsetup", "desc": "Userspace setup tool for transparent encryption of block devices using dm-crypt", "rdep": 10},
{"name": "sudo", "desc": "Give certain users the ability to run some commands as root", "rdep": 3},
{"name": "wesnoth", "desc": "A turn-based strategy game on a fantasy world", "rdep": 1},
{"name": "lxcfs", "desc": "FUSE filesystem for LXC", "rdep": 1},
{"name": "ntfs-3g", "desc": "NTFS filesystem driver and utilities", "rdep": 5},
{"name": "leptonica", "desc": "Software that is broadly useful for image processing and image analysis applications", "rdep": 2},
{"name": "gimp", "desc": "GNU Image Manipulation Program", "rdep": 2},
{"name": "pigeonhole", "desc": "Sieve implementation for Dovecot", "rdep": 1},
{"name": "fastd", "desc": "Fast and secure tunneling daemon", "rdep": 1},
{"name": "nautilus", "desc": "Default file manager for GNOME", "rdep": 4},
{"name": "unbound", "desc": "Validating, recursive, and caching DNS resolver", "rdep": 3},
{"name": "cronie", "desc": "Daemon that runs specified programs at scheduled times and related tools", "rdep": 5},
{"name": "grep", "desc": "A string search utility", "rdep": 20},
{"name": "ark", "desc": "Archiving Tool", "rdep": 1},
{"name": "bubblewrap", "desc": "Unprivileged sandboxing tool", "rdep": 10},
{"name": "freetype2-demos", "desc": "Freetype tools and demos", "rdep": 1},
{"name": "samurai", "desc": "ninja-compatible build tool written in C", "rdep": 1},
{"name": "sysstat", "desc": "a collection of performance monitoring tools (iostat,isag,mpstat,pidstat,sadf,sar)", "rdep": 1},
{"name": "lua", "desc": "Powerful lightweight programming language designed for extending applications", "rdep": 73},
{"name": "dash", "desc": "POSIX compliant shell that aims to be as small as possible", "rdep": 1},
{"name": "ruby", "desc": "An object-oriented language for quick and easy programming", "rdep": 347},
{"name": "mutt", "desc": "Small but very powerful text-based mail client", "rdep": 1},
{"name": "grub", "desc": "Include btrfs snapshots in GRUB boot options", "rdep": 6},
{"name": "lxc", "desc": "Linux Containers", "rdep": 3},
{"name": "keepalived", "desc": "Failover and monitoring daemon for LVS clusters", "rdep": 1},
{"name": "aspell", "desc": "A spell checker designed to eventually replace Ispell", "rdep": 22},
{"name": "git", "desc": "the fast distributed version control system", "rdep": 58},
{"name": "weechat", "desc": "Fast, light and extensible IRC client (curses UI)", "rdep": 1},
{"name": "cyrus-sasl", "desc": "Cyrus saslauthd SASL authentication daemon", "rdep": 1},
{"name": "iodine", "desc": "Tunnel IPv4 data through a DNS server", "rdep": 1},
{"name": "yodl", "desc": "Implements a pre-document language and tools to process it.", "rdep": 1},
{"name": "squid", "desc": "Full-featured Web proxy cache server", "rdep": 1},
{"name": "osquery", "desc": "SQL powered operating system instrumentation, monitoring, and analytics", "rdep": 1},
{"name": "bison", "desc": "The GNU general-purpose parser generator", "rdep": 2},
{"name": "networkmanager-vpnc", "desc": "NetworkManager VPN plugin for VPNC", "rdep": 1},
{"name": "cpio", "desc": "A tool to copy files into or out of a cpio or tar archive", "rdep": 4},
{"name": "gnome-bluetooth", "desc": "GNOME Bluetooth Subsystem", "rdep": 3},
{"name": "bird", "desc": "RIP, OSPF, BGP, MPLS, BFD, Babel routing daemon", "rdep": 1},
{"name": "clutter", "desc": "A toolkit for creating fast, portable, compelling dynamic UIs", "rdep": 8},
{"name": "zcash", "desc": "Permissionless financial system employing zero-knowledge security", "rdep": 1},
{"name": "vim", "desc": "Vi Improved, a highly configurable, improved version of the vi text editor", "rdep": 84},
{"name": "evolution-ews", "desc": "MS Exchange integration through Exchange Web Services", "rdep": 1},
{"name": "mumble", "desc": "An Open Source, low-latency, high quality voice chat software (client)", "rdep": 1},
{"name": "swaylock", "desc": "Screen locker for Wayland", "rdep": 1},
{"name": "iproute2", "desc": "IP Routing Utilities", "rdep": 20},
{"name": "graphite", "desc": "reimplementation of the SIL Graphite text processing engine", "rdep": 6},
{"name": "cgit", "desc": "A web interface for git written in plain C", "rdep": 1},
{"name": "tpm2-tools", "desc": "Trusted Platform Module 2.0 tools based on tpm2-tss", "rdep": 1},
{"name": "gcc", "desc": "The GNU Compiler Collection - C and C++ frontends (12.x.x)", "rdep": 29},
{"name": "evolution", "desc": "Manage your email, contacts and schedule", "rdep": 4},
{"name": "unicorn", "desc": "Lightweight, multi-platform, multi-architecture CPU emulator framework based on QEMU", "rdep": 2},
{"name": "mupdf", "desc": "Lightweight PDF and XPS viewer", "rdep": 1},
{"name": "colord", "desc": "System daemon for managing color devices", "rdep": 10},
{"name": "openldap", "desc": "Lightweight Directory Access Protocol (LDAP) client and server", "rdep": 1},
{"name": "capstone", "desc": "Lightweight multi-platform, multi-architecture disassembly framework", "rdep": 27},
{"name": "roundcubemail", "desc": "A PHP web-based mail client", "rdep": 1},
{"name": "ardour", "desc": "Professional-grade digital audio workstation", "rdep": 90},
{"name": "enlightenment", "desc": "Enlightenment window manager", "rdep": 1},
{"name": "sqlite", "desc": "SQLite Database browser is a light GUI editor for SQLite databases, built on top of Qt", "rdep": 167},
{"name": "wget", "desc": "Network utility to retrieve files from the Web", "rdep": 8},
{"name": "xrootd", "desc": "Software framework for fast, low latency, scalable and fault tolerant data access.", "rdep": 1},
{"name": "thrift", "desc": "Scalable cross-language services framework for IPC/RPC", "rdep": 2},
{"name": "cimg", "desc": "Open-source C++ toolkit for image processing", "rdep": 1},
{"name": "evolution-data-server", "desc": "Unified contacts, tasks and calendar backend", "rdep": 16},
{"name": "screen", "desc": "Full-screen window manager that multiplexes a physical terminal", "rdep": 1},
{"name": "dosfstools", "desc": "DOS filesystem utilities", "rdep": 5},
{"name": "electron", "desc": "Meta package, always depends on the latest stable Electron build", "rdep": 2},
{"name": "flac", "desc": "Free Lossless Audio Codec", "rdep": 44},
{"name": "pigz", "desc": "Parallel implementation of the gzip file compressor", "rdep": 1},
{"name": "jhead", "desc": "EXIF JPEG info parser and thumbnail remover", "rdep": 1},
{"name": "spice", "desc": "SPICE server", "rdep": 5},
{"name": "ulfius", "desc": "HTTP Framework for REST Applications in C", "rdep": 2},
{"name": "squashfs-tools", "desc": "Tools for squashfs, a highly compressed read-only filesystem for Linux", "rdep": 5},
{"name": "yubico-pam", "desc": "Yubico YubiKey PAM module", "rdep": 1},
{"name": "util-linux", "desc": "Miscellaneous system utilities for Linux", "rdep": 45},
{"name": "booth", "desc": "A convergent camera app", "rdep": 1},
{"name": "flatpak", "desc": "Linux application sandboxing and distribution framework (formerly xdg-app)", "rdep": 8},
{"name": "at-spi2-core", "desc": "Protocol definitions and daemon for D-Bus at-spi", "rdep": 24},
{"name": "opus", "desc": "Totally open, royalty-free, highly versatile audio codec", "rdep": 32},
{"name": "shadow", "desc": "A lightweight tunnel proxy", "rdep": 6},
{"name": "uwsgi", "desc": "A full stack for building hosting services", "rdep": 12},
{"name": "protobuf", "desc": "Protocol Buffers - Google's data interchange format", "rdep": 42},
{"name": "cinnamon-screensaver", "desc": "Screensaver designed to integrate well with the Cinnamon desktop.", "rdep": 1},
{"name": "pesign", "desc": "Linux tools for signed PE-COFF binaries", "rdep": 1},
{"name": "networkmanager", "desc": "Network connection manager and user applications", "rdep": 7},
{"name": "chafa", "desc": "Image-to-text converter supporting a wide range of symbols and palettes, transparency, animations, etc.", "rdep": 1},
{"name": "stunnel", "desc": "A program that allows you to encrypt arbitrary TCP connections inside SSL", "rdep": 1},
{"name": "qpdf", "desc": "QPDF: A Content-Preserving PDF Transformation System", "rdep": 4},
{"name": "guile", "desc": "Portable, embeddable Scheme implementation written in C", "rdep": 20},
{"name": "gnumeric", "desc": "A GNOME Spreadsheet Program", "rdep": 1},
{"name": "sigil", "desc": "multi-platform EPUB2/EPUB3 ebook editor", "rdep": 1},
{"name": "gthumb", "desc": "Image browser and viewer for the GNOME Desktop", "rdep": 1},
{"name": "gifsicle", "desc": "Command-line tool for creating, editing, and getting information about GIF images and animations", "rdep": 1},
{"name": "passenger", "desc": "Fast and robust web server and application server for Ruby, Python and Node.js", "rdep": 2},
{"name": "tinyproxy", "desc": "A light-weight HTTP proxy daemon for POSIX operating systems", "rdep": 1},
{"name": "luajit", "desc": "Just-in-time compiler and drop-in replacement for Lua 5.1", "rdep": 24},
{"name": "linux", "desc": "Drivers and tools to support ATM networking under Linux.", "rdep": 13},
{"name": "md4c", "desc": "C Markdown parser", "rdep": 2},
{"name": "tar", "desc": "Lua application server integrated with a database management system", "rdep": 7},
{"name": "tor", "desc": "Anonymizing overlay network.", "rdep": 3},
{"name": "lz4", "desc": "Extremely fast compression algorithm", "rdep": 44},
{"name": "opendoas", "desc": "Run commands as super user or another user", "rdep": 1},
{"name": "mailutils", "desc": "MUA command line tool (mailx)", "rdep": 1},
{"name": "radare2", "desc": "Open-source tools to disasm, debug, analyze and manipulate binary files", "rdep": 3},
{"name": "furnace", "desc": "A multi-system chiptune tracker compatible with DefleMask modules", "rdep": 1},
{"name": "logrotate", "desc": "Rotates system logs automatically", "rdep": 1},
{"name": "acpica", "desc": "ACPI tools, including Intel ACPI Source Language compiler", "rdep": 1},
{"name": "systemd", "desc": "Graphical front-end for systemd", "rdep": 111},
{"name": "nmap", "desc": "Utility for network discovery and security auditing", "rdep": 2},
{"name": "sleuthkit", "desc": "File system and media management forensic analysis tools", "rdep": 1},
{"name": "patch", "desc": "A modular patch bay for audio and MIDI systems based on Jack and Alsa", "rdep": 5},
{"name": "teeworlds", "desc": "Fast-paced multiplayer 2D shooter game", "rdep": 1},
{"name": "haproxy", "desc": "Reliable, high performance TCP/HTTP load balancer", "rdep": 1},
{"name": "pam-u2f", "desc": "Universal 2nd Factor (U2F) PAM authentication module from Yubico", "rdep": 1},
{"name": "atomicparsley", "desc": "Command line program for reading, parsing and setting metadata in MPEG-4 files", "rdep": 1},
{"name": "augeas", "desc": "A configuration editing tool that parses config files and transforms them into a tree", "rdep": 5},
{"name": "cantata", "desc": "Qt5 client for the music player daemon (MPD)", "rdep": 1},
{"name": "glewlwyd", "desc": "Single-Sign-On (SSO) server with multiple factor authentication", "rdep": 1},
{"name": "tinc", "desc": "VPN (Virtual Private Network) daemon", "rdep": 1},
{"name": "yara", "desc": "Tool aimed at helping malware researchers to identify and classify malware samples", "rdep": 2},
{"name": "milkytracker", "desc": "Music tracker inspired by Fast Tracker II", "rdep": 1},
{"name": "htmldoc", "desc": "HTML Conversion Software", "rdep": 1},
{"name": "exim", "desc": "Message Transfer Agent", "rdep": 3},
{"name": "usbredir", "desc": "USB traffic redirection protocol", "rdep": 2},
{"name": "zsh", "desc": "A very advanced and programmable command interpreter (shell) for UNIX", "rdep": 7},
{"name": "gst-plugins-good", "desc": "Multimedia graph framework - good plugins", "rdep": 32},
{"name": "graphviz", "desc": "Graph visualization software", "rdep": 19},
{"name": "x11vnc", "desc": "VNC server for real X displays", "rdep": 1},
{"name": "veracrypt", "desc": "Disk encryption with strong security based on TrueCrypt", "rdep": 1},
{"name": "profanity", "desc": "Console based XMPP client", "rdep": 1},
{"name": "upx", "desc": "Extendable, high-performance executable packer for several executable formats", "rdep": 1},
{"name": "rdesktop", "desc": "An open source client for Windows Remote Desktop Services", "rdep": 1},
{"name": "bluez", "desc": "Daemons for the bluetooth protocol stack", "rdep": 9},
{"name": "neomutt", "desc": "A version of mutt with added features", "rdep": 1},
{"name": "cups", "desc": "OpenPrinting CUPS - daemon package", "rdep": 5},
{"name": "ibus", "desc": "Next Generation Input Bus for Linux", "rdep": 17},
{"name": "file", "desc": "Create and modify archives", "rdep": 36},
{"name": "re2c", "desc": "A tool for generating C-based recognizers from regular expressions", "rdep": 1},
{"name": "unixodbc", "desc": "ODBC is an open specification for providing application developers with a predictable API with which to access Data Sources", "rdep": 16},
{"name": "wayland", "desc": "A computer display server protocol", "rdep": 89},
{"name": "openfortivpn", "desc": "An open implementation of Fortinet's proprietary PPP+SSL VPN solution", "rdep": 1},
{"name": "tcl", "desc": "Powerful, easy-to-learn dynamic programming language", "rdep": 11},
{"name": "pgbouncer", "desc": "Lightweight connection pooler for PostgreSQL", "rdep": 1},
{"name": "nbd", "desc": "tools for network block devices, allowing you to use remote block devices over TCP/IP", "rdep": 1},
{"name": "open-vm-tools", "desc": "The Open Virtual Machine Tools (open-vm-tools) are the open source implementation of VMware Tools", "rdep": 1},
{"name": "bash", "desc": "Bash Automated Testing System", "rdep": 317},
{"name": "sddm", "desc": "QML based X11 and Wayland display manager", "rdep": 1},
{"name": "lldpd", "desc": "802.1ab implementation (LLDP) to help you locate neighbors", "rdep": 1},
{"name": "mruby", "desc": "An interpreter for the Ruby programming language with the intention of being lightweight and easily embeddable", "rdep": 1},
{"name": "brotli", "desc": "Generic-purpose lossless compression algorithm", "rdep": 26},
{"name": "quagga", "desc": "BGP/OSPF/ISIS/RIP/RIPNG routing daemon suite", "rdep": 1},
{"name": "dropbear", "desc": "Lightweight SSH server", "rdep": 1},
{"name": "m4", "desc": "Algorithms for linear algebra over F_2", "rdep": 5},
{"name": "gpac", "desc": "A multimedia framework based on the MPEG-4 Systems standard", "rdep": 1},
{"name": "ettercap", "desc": "Network sniffer/interceptor/logger for ethernet LANs - console", "rdep": 1},
{"name": "gtk-vnc", "desc": "VNC viewer widget for GTK", "rdep": 4},
{"name": "connman", "desc": "Intel's modular network connection manager", "rdep": 1},
{"name": "znc", "desc": "An IRC bouncer with modules & scripts support", "rdep": 1},
{"name": "gst-plugins-bad", "desc": "Multimedia graph framework - bad plugins", "rdep": 11},
{"name": "hexchat", "desc": "A popular and easy to use graphical IRC (chat) client", "rdep": 1},
{"name": "file-roller", "desc": "Create and modify archives", "rdep": 1},
{"name": "krb5", "desc": "The Kerberos network authentication system", "rdep": 42},
{"name": "sssd", "desc": "System Security Services Daemon", "rdep": 1},
{"name": "nginx", "desc": "Lightweight HTTP server and IMAP/POP3 proxy server", "rdep": 17},
{"name": "irssi", "desc": "Modular text mode IRC client with Perl scripting", "rdep": 1},
{"name": "gnome-online-accounts", "desc": "Single sign-on framework for GNOME", "rdep": 9},
{"name": "busybox", "desc": "Utilities for rescue and embedded systems", "rdep": 1},
{"name": "atril", "desc": "MATE document viewer", "rdep": 1},
{"name": "ipmitool", "desc": "Command-line interface to IPMI-enabled devices", "rdep": 1},
{"name": "singular", "desc": "Computer Algebra System for polynomial computations", "rdep": 2},
{"name": "openvpn", "desc": "An easy-to-use, robust and highly configurable VPN (Virtual Private Network)", "rdep": 2},
{"name": "gsasl", "desc": "Simple Authentication and Security Layer framework and a few common SASL mechanisms", "rdep": 4},
{"name": "redis", "desc": "An in-memory database that persists on disk", "rdep": 2},
{"name": "thunar", "desc": "Modern, fast and easy-to-use file manager for Xfce", "rdep": 4},
{"name": "firejail", "desc": "Linux namespaces sandbox program", "rdep": 1},
{"name": "unrar", "desc": "The RAR uncompression program", "rdep": 1},
{"name": "aria2", "desc": "Download utility that supports HTTP(S), FTP, BitTorrent, and Metalink", "rdep": 4},
{"name": "nethack", "desc": "A single player dungeon exploration game", "rdep": 1},
{"name": "subversion", "desc": "A Modern Concurrent Version Control System", "rdep": 3},
{"name": "aircrack-ng", "desc": "Key cracker for the 802.11 WEP and WPA-PSK protocols", "rdep": 2},
{"name": "net-snmp", "desc": "A suite of applications used to implement SNMP v1, SNMP v2c and SNMP v3 using both IPv4 and IPv6", "rdep": 15},
{"name": "rizin", "desc": "Open-source tools to disasm, debug, analyze and manipulate binary files", "rdep": 3},
{"name": "packagekit", "desc": "A system designed to make installation and updates of packages easier", "rdep": 4},
{"name": "netdata", "desc": "Real-time performance monitoring, in the greatest possible detail, over the web", "rdep": 1},
{"name": "kde-cli-tools", "desc": "Tools based on KDE Frameworks 5 to better interact with the system", "rdep": 1},
{"name": "qcad", "desc": "A 2D CAD package based upon Qt", "rdep": 1},
{"name": "vlc", "desc": "Multi-platform MPEG, VCD/DVD, and DivX player", "rdep": 7},
{"name": "gnome-font-viewer", "desc": "A font viewer utility for GNOME", "rdep": 1},
{"name": "opensips", "desc": "An Open Source SIP Server able to act as a SIP proxy, registrar, location server, redirect server ...", "rdep": 1},
{"name": "gzip", "desc": "GNU compression utility", "rdep": 13},
{"name": "mosquitto", "desc": "An Open Source MQTT Broker", "rdep": 1},
{"name": "p11-kit", "desc": "Loads and enumerates PKCS#11 modules", "rdep": 5},
{"name": "evince", "desc": "Document viewer (PDF, PostScript, XPS, djvu, dvi, tiff, cbr, cbz, cb7, cbt)", "rdep": 5},
{"name": "menu-cache", "desc": "Caching mechanism for freedesktop.org compliant menus", "rdep": 9},
{"name": "mono", "desc": "Free implementation of the .NET platform including runtime and compiler", "rdep": 10},
{"name": "rsync", "desc": "A fast and versatile file copying tool for remote and local files", "rdep": 17},
{"name": "proxychains-ng", "desc": "A hook preloader that allows to redirect TCP traffic of existing dynamically linked programs through one or more SOCKS or HTTP proxies", "rdep": 1},
{"name": "gssproxy", "desc": "GSSAPI Proxy", "rdep": 1},
{"name": "unzip", "desc": "For extracting and viewing files in .zip archives", "rdep": 16},
{"name": "lhasa", "desc": "Free LZH/LHA archive tool", "rdep": 1},
{"name": "freerdp", "desc": "Free implementation of the Remote Desktop Protocol (RDP)", "rdep": 4},
{"name": "tk", "desc": "A windowing toolkit for use with tcl", "rdep": 8},
{"name": "lftp", "desc": "Sophisticated command line based FTP client", "rdep": 1},
{"name": "cockpit", "desc": "A systemd web based user interface for Linux servers", "rdep": 5},
{"name": "dbus", "desc": "Linux D-Bus Message Broker", "rdep": 111},
{"name": "cifs-utils", "desc": "CIFS filesystem user-space tools", "rdep": 2},
{"name": "capnproto", "desc": "Cap'n Proto serialization/RPC system", "rdep": 3},
{"name": "hivex", "desc": "System for extracting the contents of Windows Registry.", "rdep": 1},
{"name": "gvfs", "desc": "Virtual filesystem implementation for GIO", "rdep": 18},
{"name": "deepin-clone", "desc": "Disk and partition backup/restore tool", "rdep": 1},
{"name": "smb4k", "desc": "A KDE program that browses samba shares", "rdep": 1},
{"name": "389-ds-base", "desc": "389 Directory Server (base)", "rdep": 1},
{"name": "w3m", "desc": "Text-based Web browser as well as pager", "rdep": 1},
{"name": "gdm", "desc": "Display manager and login screen", "rdep": 1}
]