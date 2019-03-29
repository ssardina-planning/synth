# TLV — Temporal Logic Verifier

This is a git repo putting together the material for the TLV system and the behavior composition modules and examples.

TLV is based on the SMV model checker, however, all the code implementing model checking has been replaced by a layer that implements a scripting 
language called TLV-Basic. Users of the system can then write procedures in TLV-Basic for implementing either model checking or deductive verification 
rules. TLV is a byproduct of Elad Shahar's M.Sc. thesis. Please see [TLV HOME PAGE HERE](https://cs.nyu.edu/acsys/tlv/index.html).

There are 32-bits executable version for Linux and Windows.

## Linux

1. Get TLV system by clonning this repo or getting it from its [home page](http://www.cs.nyu.edu/acsys/tlv/index.html).
2. You will need several 32-bit libraryes. The best way to get them all is to run the following to get them all:

    sudo apt-get install ia32-libs

  One can also just install the two libraries needed:

    sudo apt-get install libncurses5:i386 libreadline5:i386

3. Get also the TLV modules and put them somewhere.
4. Set `TLV_PATH` where the TLV modules are located. For example:

    export TLV_PATH=/home/ssardina/bin/TLV/Modules/

5. Try it to make sure it works:

    [ssardina@Thinkpad-X1 Downloads]$ tlv
    Loading Util.tlv $Revision: 4.3 $
    Loading MCTL.tlv $Revision: 4.11 $
    Loading MCTLS.tlv $Revision: 4.1 $
    Loading TESTER.tlv $Revision: 4.5 $
    Loading MCsimple.tlv  $Revision: 4.13 $
    Loading SIMULATE $Revision: 4.4 $
    Loading Floyd.tlv $Revision: 4.1 $
    Loading Abstract.tlv  $Revision: 4.3 $
    Loading modified deductive.tlv $Revision: 4.9 $
    Loading compat.tlv $Revision: 1.5 $

    file TS.tlv: line 799: _sn undefined Loaded rules file Rules.tlv.

      Your wish is my command ... 


    >> 

## Cannot find library `libreadline.so.5`?

If you get an error like this one:

    [ssardina@Thinkpad-X1 tlv-linux]$ ./tlv 
    ./tlv: error while loading shared libraries: libreadline.so.5: cannot open shared object file: No such file or directory

Then, you may not have the 32-bits version`libreadline.so.5` library.

First, you can find out all the libraries that `tlv` needs and where it has found them:

    [ssardina@Thinkpad-X1 tlv-linux]$ ldd ./tlv 
	linux-gate.so.1 (0xf7fa6000)
	libm.so.6 => /lib/i386-linux-gnu/libm.so.6 (0xf7e5c000)
	libreadline.so.5 => not found
	libncurses.so.5 => /lib/i386-linux-gnu/libncurses.so.5 (0xf7e36000)
	libc.so.6 => /lib/i386-linux-gnu/libc.so.6 (0xf7c5a000)
	/lib/ld-linux.so.2 (0xf7fa8000)
	libdl.so.2 => /lib/i386-linux-gnu/libdl.so.2 (0xf7c55000)
	libtinfo.so.5 => /lib/i386-linux-gnu/libtinfo.so.5 (0xf7c32000)

In this case, `libreadline.so.5` couldn't be found. The So you install them as f

    sudo apt-get install lib32readline5

or

    sudo apt-get install libreadline5:i386
    
This should have fixed the issue:

    [ssardina@Thinkpad-X1 Downloads]$ ldd tlv
	linux-gate.so.1 (0xf7eec000)
	libm.so.6 => /lib/i386-linux-gnu/libm.so.6 (0xf7de5000)
	libreadline.so.5 => /lib32/libreadline.so.5 (0xf7d69000)
	libncurses.so.5 => /lib/i386-linux-gnu/libncurses.so.5 (0xf7d43000)
	libc.so.6 => /lib/i386-linux-gnu/libc.so.6 (0xf7b67000)
	/lib/ld-linux.so.2 (0xf7eee000)
	libtinfo.so.5 => /lib/i386-linux-gnu/libtinfo.so.5 (0xf7b44000)
	libdl.so.2 => /lib/i386-linux-gnu/libdl.so.2 (0xf7b3f000)

    


## Composition Example



5. Run an example:

   tlv comp-inv.pf painting_arms_kr08-v2.smv

See you need to give TLV the library/module (here `comp-inv.pf`) that will is to be used.

In this example `comp-inv.pf` uses `synt-inv.tlv` which is a synthesis for safety games: (\G p)-games


