# Data types and Match

Hakaru with several built-in data types.

* Pair
* Unit
* Either
* Bool

## Match

We use `match` to deconstruct out data types
and access their elements.

````nohighlight
match (1,2):
  (x,y): x + y
````
