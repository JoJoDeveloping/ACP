# First-Order Reification

## What is this

This is a MetaCoq library for ACP, a course held at Saarland university about Advanced Coq Programming.
It takes certain Coq terms and reifies them into a First-Order logic theory, to then prove things about this theory in Coq without having to specify terms in yet another syntax.

## How to use?

Examples are given in PA.v or ZF.v. You define an instance of `tarski_reflector`, and then you can use the `represent.` and `representNP.` tactics.
PA.v also shows how to write extension points.

You can compile everything (including the samples, which do some printing) using the Makefile (i.e. run `make`. You of course need GNU make).

The project is written agains Coq 8.12 and MetaCoq. To create an opam environment with the exact dependencies, run the following commands:
```
opam switch create reification 4.09.1+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-metacoq.1.0~beta1+8.12
```

## I want to know more! Why is this documentation so short?

For more information, see the related [PDF documentation](https://github.com/JoJoDeveloping/ACP/blob/master/documentation/doc.pdf) or the [CoqDoc](https://jojodeveloping.github.io/ACP/GeneralReflection.html).
If you are not viewing this file on GitHub, you should do so. Find the repository here: https://github.com/JoJoDeveloping/ACP

