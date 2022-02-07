* [Documentation](https://docs.rs/mexset/)
* [Crate](https://crates.io/crates/mexset)


## Description

The MexSet data structure is an implementation of a set that can quickly find **MEX**.

*The MEX (Minimum EXcluded) of a subset of the set of natural numbers is the minimum natural number missing from this subset.
That is, it is the minimum value of the [complement](https://en.wikipedia.org/wiki/Complement_(set_theory)) set.*


## Usage

As a library

```rust
use mexset::MexSet;

let mut set: MexSet<u32> = MexSet::new();
assert_eq!(set.minimum_excluded(), 0);   // The MEX of an empty set is 0

set.insert(2); 
set.insert(1);
assert_eq!(set.minimum_excluded(), 0);   // 0 is the smallest missing number

set.insert(0);
assert_eq!(set.minimum_excluded(), 3);   // mex({0, 1, 2}) = 3

set.insert(4);
assert_eq!(set.minimum_excluded(), 3);   // mex({0, 1, 2, 4}) = 3

set.insert(3);
assert_eq!(set.minimum_excluded(), 5);   // mex({0, 1, 2, 3, 4}) = 5

set.remove(&1);
assert_eq!(set.minimum_excluded(), 1);  // mex({0, 2, 3, 4}) = 1
```

If you have any comments or suggestions, or you suddenly found an error, please start a new issue or pool request.
