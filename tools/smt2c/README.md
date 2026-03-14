# smt2c


## Compiling

First, install CBMC somewhere on your machine: 
https://github.com/diffblue/cbmc/

The install instructions are here:
https://github.com/diffblue/cbmc/blob/develop/COMPILING.md

smt2c has been tested with CBMC commit `e88ed5f7661c896e3c3f11212edc99373607d4da` (the head commit of the develop branch as of 11am 7th July 2025)

Then edit smt2c/config.inc so that it points to the directory containing CBMC, e.g., mine is in `/Users/elipol/cbmc`:
~~~
CPROVER_DIR ?= /Users/elipol/cbmc
~~~

Then compile smt2c using make:
~~~
cd smt2c/src
make
~~~

## Running

The binary is called smt2c, and can be found in 'smt2c/src/smt2c'

To see the instructions on running smt2c, run 'smt2c --help'

It takes 1 command line argument, which is the function to be translated. For example

~~~
smt2c "(define-fun plus2 ((b1 Int) (b2 Int)) Int ( + b1 b2))"
~~~

produces the result:
~~~
integer plus2(integer b1, integer b2) {
  return b1 + b2;
}
~~~

It supports bitvectors and booleans, for example 
~~~
smt2c "(define-fun shesh ((x (_ BitVec 64))) (_ BitVec 64)
    (bvlshr x #x0000000000000010))"

~~~

produces the result:
~~~
unsigned long int shesh(unsigned long int x) {
  return x >> 16;
}
~~~






