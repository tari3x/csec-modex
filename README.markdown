
This is an implementation of the verification method described in 
"Extracting and Verifying Cryptographic Models from C Protocol Code by Symbolic Execution" 
and 
"Computational Verification of C Protocol Implementations by Symbolic Execution" 
by Mihhail Aizatulin, Andy Gordon, and Jan Jürjens.

The distribution includes the source code of the protocols analysed in the papers: CSur,
simple mac, simple xor, RPC, RPC-enc, and NSL. Unfortunately, we are not able to distribute the source code 
of the metering protocol, due to licensing restrictions.

Download
========

    git clone --recursive git://github.com/tari3x/csec-modex.git

Do not use the zip file provided by github, as it breaks symbolic links in the openssl source.
	
Dependencies
============

The distribution bundles and automatically builds most of the dependencies. 
The following dependencies require some extra work:

- gcc and ocaml need to be installed on the system

- Yices SMT solver, which we are not allowed to redistribute due to licensing restrictions. 

    The tools are known to work with version 1.0.28/1.0.29 with dynamically linked GMP which you can obtain from
      http://yices.csl.sri.com/
	  
    First make sure that the appropriate version of GMP (static or dynamic, as used by yices) is installed.
    You can then use the script
      deps/ocamlyices/install-yices.sh
    to install yices.

- camlidl. You can get it with opam by running "opam install camlidl".

- the curses library (libncurses-devel in Cygwin) is required by CIL

How to use
==========

The distribution relies on a unix environment and cmake for building. 
To build all the tools and run the verification experiments install cmake and run

    cmake .
    make

The first run of make will likely be cluttered with output.
When running make the second time you should see verification output of the kind:

    $ make
    [  0%] Generating src/symtrace/imltrace.exe, src/symtrace/pitrace.exe
    [ 24%] Built target CSur
    [ 24%] Generating src/symtrace/imltrace.exe, src/symtrace/pitrace.exe
    RESULT ev:endB() ==> ev:notA() is false.
    RESULT ev:endB() ==> ev:beginA() | ev:notA() is true.
    [ 48%] Built target NSL
    [ 48%] Generating src/symtrace/imltrace.exe, src/symtrace/pitrace.exe
    RESULT not ev:client_accept(x_31,y_32) is false.
    RESULT ev:server_reply(x_310,y_311) ==> ev:client_begin(x_310) is true.
    RESULT ev:client_accept(x_434,y_435) ==> ev:server_reply(x_434,y_435) is true.
    [ 73%] Built target RPC
    [ 73%] Generating src/symtrace/imltrace.exe, src/symtrace/pitrace.exe
    RESULT not ev:server_recv(x_11) is false.
    RESULT ev:server_recv(x_121) ==> ev:client_send(x_121) is true.
    [100%] Built target simple_hash
	
To check that the IML and the pi calculus output correspond to the good output run 

    make check

This might fail, because the reference output was produced on a 64 bit machine and 
this influences the format of the network messages. In future this shall be fixed by
transition to an architecture-independent implementation.

Contact
=======

Please send bug reports and suggestions to Mihhail Aizatulin (<avatar@hot.ee>)

When submitting bug reports please include the full output of running make together
with all the *.debug.out files from the test folder in which an error happened.
