# Data types and Match

Hakaru with several built-in data types.

* pair
* unit
* either
* bool

## Match

We use `match` to deconstruct out data types
and access their elements.

````nohighlight
match left(3). either(int,bool):
  left(x) : 1
  right(x): 2
````

We do include special syntax for pairs

````nohighlight
match (1,2):
  (x,y): x + y
````
