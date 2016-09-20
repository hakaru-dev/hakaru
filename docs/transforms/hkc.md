# HKC Compilation

`hkc` is a command line tool to compiler Hakaru programs to C.


## Measures

Measures compile to programs that sample from a distributions.

````
uniform(0,1)
````

Will produce the sampler:

````
#include <time.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>

double measure(double * s_a)
 {
    *s_a = ((double)0) + ((double)rand()) / ((double)RAND_MAX) * ((double)1) - ((double)0);
    return 0;
 }

int main()
 {
    double sample;
    while (1)
    {
        measure(&sample);
        printf("%.17f\n",sample);
    }
    return 0;
 }
````

The `-F` flag will produce a function that draws a single sample from a
distribution.



## Lambdas

Lambdas compile to functions in C:

````
fn x array(real):
  (summate i from 0 to size(x): x[i])
   *
  prob2real(recip(nat2prob((size(x) + 1))))

````

Becomes:

````
#include <stdlib.h>
#include <stdio.h>
#include <math.h>

struct arrayReal {
 int size; double * data;
  };

double fn_a(struct arrayReal x_b)
 {
     int i_c;
     double acc_d;
     double p_e;
     double _f;
     double r_g;
     acc_d = 0;
     for (i_c = 0; i_c < x_b.size; i_c++)
     {
        p_e = log1p(1 + x_b.size - 1);
        _f = log1p(1 / expm1(p_e + 1) - 1);
        r_g = expm1(_f) + 1;
        acc_d += r_g * *(x_b.data + i_c);
     }
     return acc_d;
 }
````

Using the `-F` flag will allow the user to add their own name to a function,
otherwise the name is chosen automatically as "fn_<unique identifier>".


## Building C Types

In order to connect `hkc` generated code to external C code, we will need to
know how a Hakaru type will look in C.

<!-- nat should be an unsigned int in the future -->
`int` and `nat` both become a C `int`. `real` is turned into a C `double`.
`prob` types are also turned into C `double` types, but these are in the log
domain. Therefore, we must take the log of our data before handing to `hkc` code
and take the exp of it when using the result.

Hakara arrays, like `array(int)` will be represented as structs with two
elements: an `int` called "size" representing the length of the array and a
pointer to the data called "data" contained in the struct. `hkc` will
automatically generate these struct declarations if they are needed in the
program. Their names do not change.

````
struct arrayNat {
  int size; int * data;
  };

struct arrayInt {
  int size; double * data;
  };

struct arrayProb {
  int size; double * data;
  };

struct arrayReal {
  int size; double * data;
  };
````


## Extra Options
