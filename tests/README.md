# Hakaru Tests #

These tests are run using `stack test`. They are included in the test cases found in `hakaru/haskell/Tests/RoundTrip.hs`, which is picked up in
`hakaru/haskell/Tests/TestSuite.hs`.

| Program | Expected Output | Purpose |
|:--------|:----------------|:--------|
| t75_in.hk | t75_out.hk | Tests the `simplify` transform |