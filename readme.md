## Boolean logic for Felix

This project adds boolean logic to [Felix](https://github.com/conal/felix) for synthesis of correct hardware.

Modules in this project:

*   `Felix.Boolean`: A class `Boolean` of objects `B` and corresponding class `Logic` of morphisms for some standard operations on these "booleans".
    The vocabulary is aimed at hardware synthesis and so chooses standard gates like `nand` and `nor` as primitive with their positive counterparts (`and` and `or`) as derived operations.
*   `Felix.Boolean.Homomorphism`: Homomorphisms over the `Logic` operations, used (as always in Felix an in denotational design) to defining correctness.
*   `Felix.Boolean.Function`: The common interpretation ("denotation") of booleans as a type (`Set`), and logic operations as functions.
*   `Felix.Boolean.All`: Load this module after code changes to check validity of all of the other modules.
