# Abstract Binding Trees

Hakaru makes use of many program transformations in its codebase.
Because of this, a special mechanism is included for handing
variable bindings and substitutions. We abstract this into its
own typeclass called `ABT`.

Below is an excerpt of this typeclass

````haskell
class ABT (syn :: ([k] -> k -> *) -> k -> *) (abt :: [k] -> k -> *) | abt -> syn where
    -- Smart constructors for building a 'View' and then injecting it into the @abt@.
    syn  :: syn abt  a -> abt '[] a
    var  :: Variable a -> abt '[] a
    bind :: Variable a -> abt xs b -> abt (a ': xs) b
    caseBind :: abt (x ': xs) a -> (Variable x -> abt xs a -> r) -> r
    ...
````
