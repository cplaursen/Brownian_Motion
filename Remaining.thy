theory Remaining
  imports Brownian_Motion
begin

text \<open> Objective: Construct a Brownian motion process that satisfies locale brownian_motion \<close>

lemma "\<exists>X. brownian_motion X"
  sorry

text \<open> Subobjective 1: construct a process with independent normal increments \<close>

text \<open> We are going to do this by constructing the infinite product space specified by the 
  @{term Wiener_kernel} Markov semigroup.

  For this we need to:
\<close>
text \<open>Prove that Wiener_kernel is a Markov semigroup\<close>
thm Wiener.markov_semigroup_axioms

text \<open>Prove that Markov semigroups generated processes with independent increments\<close>
thm consistent_family_def

text \<open> I need to find the right way to construct the kernel semidirect product for PiK. It's
  proving difficult because characterising the measures is not trivial. Came up with 
  @{term PiK_semidirect_product}. Need to show that it forms a measure, it's really messy, but
  it should have the right form. It might be better to simply define PiK in a way that works well
\<close>

text \<open>Prove that the finite product of the convolution is equal to the product measure\<close>
thm prob_space.kernel_product_convolution

text \<open>Formalise the semidirect product with PiK using insert\<close>


text \<open> Subobjective 2: Finish the proof of the Kolmogorov-Chentsov theorem \<close>

text \<open> I'm missing two parts: convergence in measure implies equality of limits, and approximation
  using dyadic intervals at the limit. It would also be useful to construct the continuous
  modification explicitly, something akin to the projective limit construction. \<close>

text \<open> Subobjective 3: Show that the above process satisfies the requirements of the Kolmogorov-Chentsov
  theorem, in order to satisfy our last requriement. Further, show that modifications retain the
  independent increments. \<close>

text \<open> Theorems left to prove: \<close>

text \<open> Finite kernel product of convolution kernels is equal in distribution to product measure \<close>
thm prob_space.kernel_product_convolution

text \<open> Finite products defined by consistent family form a projective family \<close>
thm real_consistent_family.P'_projective_family

text \<open> Wiener process satisfies the Markov semigroup axioms \<close>
thm Wiener_kernel_semigroup.markov_semigroup_axioms

text \<open> Brownian motion process is a Brownian motion \<close>
thm brownian_motion_process
end