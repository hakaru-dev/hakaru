# Normalize

We also provide a `normalize` command. This command takes as input a
program representing any measure and reweights it into a program
representing a probability distribution.

For example in a slightly contrived example, we can weight a normal
distribution by two. Normalizing it will then remove this weight.

````
> echo "weight(2, normal(0,1))" | normalize | simplify -
normal(0, 1)
````