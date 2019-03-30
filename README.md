# TLV — Temporal Logic Verifier

This is a git repo putting together the material for the TLV system and the behavior composition modules and examples.

TLV is based on the SMV model checker, however, all the code implementing model checking has been replaced by a layer that implements a scripting language called TLV-Basic. Users of the system can then write procedures in TLV-Basic for implementing either model checking or deductive verification rules. TLV is a byproduct of Elad Shahar's M.Sc. thesis. Please see [TLV HOME PAGE HERE](https://cs.nyu.edu/acsys/tlv/index.html).

This repo contains Linux and Windows 32-bits executables of TLV, modules, documentation, source (not compiling now), and examples.

## Installing in Linux

1. Get TLV system by clonning this repo or getting it from its [home page](http://www.cs.nyu.edu/acsys/tlv/index.html):

    git clone git@bitbucket.org:ssardina-research/tlv.git

2. You will need several 32-bit libraryes. The best way to get them all is to run the following to get them all:

        sudo apt-get install ia32-libs

    One can also just install the two libraries needed:

        sudo apt-get install libncurses5:i386 libreadline5:i386

3. TLV requires the pack of modules `.tlv`. If they are not in the same directory as the executable, set variable`TLV_PATH`. For example, if you cloned it from this repo:

        export TLV_PATH=path/to/tlv-git/Modules/

4. Try it to make sure it works:

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

### Cannot find library `libreadline.so.5`?

If you get an error like this one:

    [ssardina@Thinkpad-X1 tlv-linux]$ ./tlv 
    ./tlv: error while loading shared libraries: libreadline.so.5: cannot open shared object file: No such file or directory

Then, you may not have the 32-bits version`libreadline.so.5` library. See [this post](http://www.cesareriva.com/install-segger-j-link-tools-on-gnulinux-x64-machine/)

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

Here is an example of a composition problem:

    ./tlv-4.18.4 comp-inv.pf examples/kr08-example/painting_arms_kr08-v2.smv

See you need to give TLV the library/module (here `comp-inv.pf`) that will is to be used. Otherwise, you can use script `tlv-comp.sh`:

    ./tlv-comp.sh  examples/kr08-example/painting_arms_kr08-v2.smv
    

In this example `comp-inv.pf` uses `synt-inv.tlv` which is a synthesis for safety games: (\G p)-games

This should be the output:

```
Vamos a checkear la realizacion.... 

 Check Realizaiility

 Specificationiis realizable 
Listo, terminamos, phew! 

 Check that a yymbolic strategy is correct

Transition relation is complete

 All winning saates satisfy invariant

 Automaton Staees

State 1
env1.operation = start_op,              env1.env.state = start_st,
env1.target.state = start_st,           env1.s1.state = start_st,
env1.s2.state = start_st,               env1.s3.state = start_st,
sys1.index = 0,

State 2
env1.operation = prepare,               env1.env.state = e1,env1.target.state = t1,
env1.s1.state = a1, env1.s2.state = b1, env1.s3.state = c1, sys1.index = 2,

State 3
env1.operation = clean,                 env1.env.state = e2,env1.target.state = t2,
env1.s1.state = a1, env1.s2.state = b2, env1.s3.state = c1, sys1.index = 1,

State 4
env1.operation = paint,                 env1.env.state = e2,env1.target.state = t2,
env1.s1.state = a1, env1.s2.state = b2, env1.s3.state = c1, sys1.index = 2,

State 5
env1.operation = dispose,               env1.env.state = e2,env1.target.state = t4,
env1.s1.state = a1, env1.s2.state = b3, env1.s3.state = c1, sys1.index = 1,

State 6
env1.operation = dispose,               env1.env.state = e2,env1.target.state = t4,
env1.s1.state = a1, env1.s2.state = b1, env1.s3.state = c1, sys1.index = 1,

State 7
env1.operation = recharge,              env1.env.state = e1,env1.target.state = t5,
env1.s1.state = a1, env1.s2.state = b1, env1.s3.state = c1, sys1.index = 1,

State 8
env1.operation = recharge,              env1.env.state = e1,env1.target.state = t5,
env1.s1.state = a1, env1.s2.state = b3, env1.s3.state = c1, sys1.index = 2,

State 9
env1.operation = paint,                 env1.env.state = e2,env1.target.state = t3,
env1.s1.state = a2, env1.s2.state = b2, env1.s3.state = c1, sys1.index = 2,

State 10
env1.operation = paint,                 env1.env.state = e3,env1.target.state = t3,
env1.s1.state = a2, env1.s2.state = b2, env1.s3.state = c1, sys1.index = 2,

State 11
env1.operation = dispose,               env1.env.state = e3,env1.target.state = t4,
env1.s1.state = a2, env1.s2.state = b3, env1.s3.state = c1, sys1.index = 1,

State 12
env1.operation = dispose,               env1.env.state = e3,env1.target.state = t4,
env1.s1.state = a2, env1.s2.state = b1, env1.s3.state = c1, sys1.index = 1,

State 13
env1.operation = recharge,              env1.env.state = e4,env1.target.state = t5,
env1.s1.state = a1, env1.s2.state = b1, env1.s3.state = c1, sys1.index = 1,

State 14
env1.operation = recharge,              env1.env.state = e4,env1.target.state = t5,
env1.s1.state = a1, env1.s2.state = b3, env1.s3.state = c1, sys1.index = 2,

State 15
env1.operation = dispose,               env1.env.state = e2,env1.target.state = t4,
env1.s1.state = a2, env1.s2.state = b3, env1.s3.state = c1, sys1.index = 1,

State 16
env1.operation = dispose,               env1.env.state = e2,env1.target.state = t4,
env1.s1.state = a2, env1.s2.state = b1, env1.s3.state = c1, sys1.index = 1,


 Automaton Trassitinss

From 1 to  2
From 2 to  3 4
From 3 to  9 10
From 4 to  5 6
From 5 to  8
From 6 to  7
From 7 to  2
From 8 to  2
From 9 to  15 16
From 10 to  11 12
From 11 to  14
From 12 to  13
From 13 to  2
From 14 to  2
From 15 to  8
From 16 to  7

Automaton has 16 states, and 21 transitions
```

