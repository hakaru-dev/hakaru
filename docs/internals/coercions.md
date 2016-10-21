# Coercions

For convenience, Hakaru offers functions to convert between the four
different numeric types in the language. These types are

* nat - Natural numbers
* int - Integers
* prob - Positive real numbers
* real - Real numbers

Amongst these types there are a collection of safe and unsafe
coercions. A safe coercion is one which is always guaranteed to
be valid. For example, converting a `nat` to an `int` is always
safe. Converting an `int` to a `nat` is unsafe as the value can
negative, and lead to runtime errors.
