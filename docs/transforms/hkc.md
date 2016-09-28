# HKC Compilation

`hkc` is a command line tool to compiler Hakaru programs to C. HKC was
created with portability and speed in mind. More recently, OpenMP support is
being added to gain more performance on multi-core machines. Basic command line
usage of HKC is much like other compilers:

```
hkc foo.hk -o foo.c
```

It is possible to go straight to an executable with the `--make ARG` flag, where
the argument is the C compiler you would like to use.




## Type Conversions

The types available in Hakaru programs are the following: `nat`, `int`, `real`,
`prob`, `array(<type>)`, `measure(<type>)`, and datum like `true` and `false`.

`nat` and `int` have a trivial mapping to the C `int` type. `real` becomes a C
`double`. The `prob` type in Hakaru is stored in the log-domain to avoid
underflow. In C this corresponds to a `double`, but we first take the log of it
before storing it, so we have to take the exp of it to bring it back to the real
numbers.

Arrays become structs that contain the size and a pointer to data stored within.
The structs are generated at compile time, but there are only four which are
named after the type they contain. Here they all are:

````
struct arrayNat {
  int size; int * data;
};

struct arrayInt {
  int size; int * data;
};

struct arrayReal {
  int size; double * data;
};

struct arrayProb {
  int size; double * data;
};
````



## Measures

Measures compile to C functions that take a location for a sample, return the
weight of the measure and store a sample in the location is was given. A simple
example is `uniform(0,1)` a measure over type `real`.


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

Recall that weights have type `prob` and are stored in the log-domain. This
example has a weight of 1.

Calling `hkc` on a measure will create a function like the one above and also a
main function that infinitely takes samples. Using `hkc -F ARG` will produce
just the function with the name of its argument.




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
   unsigned int i_c;
   double acc_d;
   double p_e;
   double _f;
   double r_g;
   acc_d = 0;
   for (i_c = 0; i_c < x_b.size; i_c++)
   {
     acc_d += *(x_b.data + i_c);
   }
   p_e = log1p(((1 + x_b.size) - 1));
   _f = -p_e;
   r_g = (expm1(_f) + 1);
   return (r_g * acc_d);
 }
````

Using the `-F` flag will allow the user to add their own name to a function,
otherwise the name is chosen automatically as `fn_<unique identifier>`.





## Computations

When compiling a computation, HKC just creates a main function to compute the
value and print it. For example:

```
summate i from 1 to 100000000:
  nat2real(i) / nat2real(i)
```

becomes:

```C
#include <stdlib.h>
#include <stdio.h>
#include <math.h>

int main()
 {
    double result;
    int i_a;
    double acc_b;
    double _c;
    acc_b = 0;
    for (i_a = 1; i_a < 100000000; i_a++)
    {
       _c = (1 / ((double)i_a));
       acc_b += (_c * ((double)i_a));
    }
    result = acc_b;
    printf("%.17f\n",result);
    return 0;
 }
```




## Parallel Programs

Calling HKC with the `-j` flag will generate the code with parallel regions to
compute the value. The parallel code uses OpenMP directives. To check if you're
compiler supports OpenMP, check [here](http://openmp.org/wp/openmp-compilers/).

For example, GCC requires the `-fopenmp` flag for OpenMP support:
```
hkc -j foo.hk -o foo.c
gcc -lm -fopenmp foo.c -o foo.bin
```
