
1) Get TLV system: http://www.cs.nyu.edu/acsys/tlv/index.html

2) Install all i386 32-bits library or you will get errors with libncurses.so.5:

    sudo apt-get install ia32-libs

One can also just install the two libraries needed:


    sudo apt-get install libncurses5:i386 libreadline5:i386

3) Get also the TLV modules and put them somewhere

4) set TLV_PATH where the TLV modules are located:

export TLV_PATH=/home/ssardina/bin/TLV/


5) Run an example:

   tlv comp-inv.pf painting_arms_kr08-v2.smv

See you need to give TLV the library/module that will be used.

In this example com-inv.pf uses synt-inv which is a synthesis for safety games: (\G p)-games


