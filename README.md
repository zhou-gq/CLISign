# CLISign: certificateless signature scheme based on DJP and SQISign

This code implements CLISign: a certificateless signature scheme based on DJP and SQISign.

(C) 2020, The SQISign team. MIT license.
(C) 2022, The CLISign team. MIT license.


## Dependencies

The code depends on the latest stable version of the [PARI/GP
library](http://pari.math.u-bordeaux.fr/), 2.11.4.

The code has an optional dependency on [GMP](https://gmplib.org/),
which is also an optional dependency of PARI/GP and is typically
installed along with it.

## Supported platforms

The code compiles and runs on Linux.

It contains an implementations of the low-level arithmetic functions based on GMP.

## Compile

To compile, test and benchmark, run

```
make
make check
make benchmark
```
