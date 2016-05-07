# Functions

Functions can be defined using a Python-inspired style syntax. One
notable difference is that each argument must be followed by its
type.

````nohighlight
def add(x real, y real):
    x + y
	
add(4,5)
````

We may optionally provide a type for the return value of a function if
we wish.

````nohighlight
def add(x. real, y. real) real:
    x + y
	
add(4,5)
````

## Anonymous functions

If you don't wish to name your functions, we also offer a syntax
for anonymous functions. These only take on argument and must be
given a type alongside the variable name.

````nohighlight
fn x real: x + 1
````

Internally, there are only one argument anonymous functions, and
lets. The first example is equivalent to the following.

````nohighlight
add = fn x real:
         fn y real:
		    x + y
add(4,5)
````
