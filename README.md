# Wiener Process in Isabelle/HOL

In this repository we formalise the theory of stochastic kernels, holder continuity, stochastic processes, and aim to construct the Wiener process.

There are two main parts to this development: the theory of stochastic kernels, and the Kolmogorov-Chentsov theorem. Common to both of them is the basic theory of stochastic processes, developed in Stochastic_Process.

## Stochastic kernels
Kernels are defined in thery Kernel. In theory Kernel_Product we define a variety of products: binary, partial, semidirect, and finite. Kernel_Composition defines composition of kernels, and its relation to the kernel product. Finally, Markov_Semigroup defines well-behaved collections of kernels, and shows how we can construct stochastic processes from these.

## Kolmogorov-Chentsov theorem
The theorem resides in Continuous_Modification, but there are a number of supporting theories for this:
 - Holder_Continuous: a theory of Holder continuity, which is a strong version of continuity that generalises Lipschitz continuity
 - Dyadic_Interval: intervals of dyadic rationals needed for an approximation argument using a countable dense set.
 - Measure_Convergence: convergence of random variables in measure.

## Applications: Wiener process and random walk.
In Wiener_Process we put all these together to construct Brownian Motion. We give a simpler example in Random_Walk of a simple random walk on the integers, constructed as a raw stochastic process and then as a stochastic kernel.
