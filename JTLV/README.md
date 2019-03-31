# JTLV  - Java TLV Verifier

JTLV is a new tool aimed to facilitate and provide a unified framework for developing formal verification algorithms in a high level programming environment.

Plase refer to the original [JTLV Home Page](http://jtlv.ysaar.net/)

# Setup & Run

Notes April 8, 2015

First, compile the Buchi Game solver:

    mkdir bucchi-solver   // where to place the compiled class files
    javac -classpath jtlv-prompt1.4.1.jar -d bucchi-solver/ BuchiGame.java

Then, you can simply run the example as follows

    java -classpath bucchi-solver/:jtlv-prompt1.4.1.jar BuchiGame examples/simpleagent4.smv


Program `simpleagent4.smv` is a running example of a planning program written by a student of Fabio Patrizi.


This should print the controller if solvable:

    SMV input module: simpleagent4.smv
    realizzabile
    Automaton states
    State 0 : <p:0, q:0, r:0, s:0, pstate:tinit, req:reqinit, action:start_op, initial:1, last:0, violated:0>
    State 1 : <p:1, q:0, r:1, s:0, pstate:t1, req:req2, action:b, initial:0, last:0, violated:0>
    State 2 : <p:1, q:0, r:1, s:0, pstate:t
    .....
    ...
    ...
    From 35 to 33 
    From 36 to 23 24 
    Automaton has 37 states and 64 transitions


NOTE: Please read Fabio's email on how the smv file should be built


## JTL format

(Notes from Fabio Patrizi, April 2, 2015).

To make the original TLV `.smv` files compliant with JTLV you have to:

1. remove the keyword "system" from the declaration of modules environment and agent in the `main`.
2. add "TRUE &" as first line in the `TRANS` section, whenever it starts with a `case` statement (this is what gave me the exception; there must be some bug).




