# 0.2.0

Unreleased

* Generalized `Arena` to support arbitrary integer types for indices and generations

# 0.1.3

Released 2019-06-09.

* Added `Debug`, `Eq`, `PartialEq`, `Ord`, `PartialOrd` and `Hash` impls to `Index<T>` even when `T` did not have them
* Ensured `Index<T>` always has `Send` and `Sync` impls, even when `T` does not (without using unsafe code)
* Fixed compilation error in benches

# 0.1.2

Released 2019-06-09.

* Fixed bugs with documentation

# 0.1.1

Released 2019-06-09.

* Fixed bugs with documentation


# 0.1.0

Released 2019-06-09.

* Forked from `generational-arena` (https://github.com/fitzgen/generational-arena/)
