# The nat type

## Inductive definitions

By inductive what we really mean is that
the values of a type can be cosntructed
from smaller values of the same type.

We see this in the case of natural numbers.
You can think of them as nested dolls, with
a solid doll at the center representing the
natural number, zero.

To represent one, we add a shell doll
around the zero doll. To represent two, we
add a shell doll around the one doll. To
represent three, we add a shell down around
the two doll, which of course is a shell
around the one doll, which is a shell
around the zero doll, which, finally, is
a solid doll.

Now writing functions that operate on
values of such a type leads naturally to
the definition of recursive functions.
