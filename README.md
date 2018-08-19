Comparing two defunctionalization strategies.
=============================================

## What is this?

The first such closure converting transformation is called defunctionalization,
and it was introduced by John C. Reynolds in 1968.

He presented it as an ad-hoc transformation in the paper
"J. C. Reynolds, Definitional interpreters for higher-order programming languages".
Here, Reynolds introduces the terms defining and defined language of an interpreter,
and explains that some properties of the defining language, such as the order of execution,
may be inherited into the defined one.

In the remaining article, Reynolds’s focus is mainly a problem he has with
controlling the call-convention (Call-by-name/Call-by-value) in an interpreter
he is writing, where it turns out to be preferable to write an interpreter for his
higher-order defined language, in a defining language which is first order.
He obtains such an interpreter by transforming an existing
interpreter written in a higher-order language into a similar first order language.

Since then closure-converting transformtions has been resarched rather thoruougly,
and in this mini-project I implement Reynolds's transformation, along with a
transformation based on a control-flow analysis called CFA-0.

## Usage.

To run the program type (assuming you have "stack" installed).

> `stack runhaskell -- ./defun-code.hs flag file`

where `flag` is one of `-naive` or `-cfa`, and `file` is the path to some file written
in pcf. The output is an sml-program which is printed to terminal. So, to save your output
you may write something like:

> `stack runhaskell -- ./defun-code.hs flag inputfilepath > outputfilepath`