# First-Order Reification

## What is this

This is a MetaCoq library for ACP, a course held at Saarland university about Advanced Coq Programming.
It takes certain Coq terms and reifies them into a First-Order logic theory, to then prove things about this theory in Coq without having to specify terms in yet another syntax.

## How to use?

Examples are given in PA.v or ZF.v. You define an instance of `tarski_reflector`, and then you can use the `represent.` and `representNP.` tactics.

## I want to know more! Why is this documentation so short.

For more information, see the related [PDF documentation](https://github.com/JoJoDeveloping/ACP/blob/master/documentation/doc.pdf) or the [CoqDoc](https://github.com/JoJoDeveloping/ACP/blob/master/GeneralReflection.v).

