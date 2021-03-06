theory POLocales
imports Main
begin
(*see notebook for extended notes*)

(*Parameter of this locale is le*)
locale partial_order =
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  assumes refl [intro, simp]: "x \<sqsubseteq> x"
    and anti_sym [intro]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> x \<rbrakk> \<Longrightarrow> x = y"
    and trans [trans]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"

print_locales

print_locale partial_order

print_locale! partial_order

(*locale predicate definition*)
thm partial_order_def
(*equivalent to original assumptions - turned into conclusions*)

definition (in partial_order)
  less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubset>" 50)
  where "(x \<sqsubset> y) = (x \<sqsubseteq> y \<and> x \<noteq> y)"

(*generates foundational constant:*)
thm "partial_order.less_def"

(*derivation of transitivity law for strict ordering*)
lemma (in partial_order) less_le_trans [trans]:
  "\<lbrakk> x \<sqsubset> y; y \<sqsubset> z \<rbrakk> \<Longrightarrow> x \<sqsubset> z"
  unfolding less_def by (blast intro: trans)

(*commands inside context block refer to a single target (partial_order)*)
context partial_order
  begin

  (*infinum (greatest lower bound of po)*)
    definition is_inf where 
      "is_inf x y i = (i \<sqsubseteq> x \<and> i \<sqsubseteq> y \<and> (\<forall>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> i))"

  (*suprenum (least upper bound)*)
    definition is_sup where
      "is_sup x y s = (x \<sqsubseteq> s \<and> y \<sqsubseteq> s \<and> (\<forall>z. x \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> s \<sqsubseteq> z))"

    theorem inf_uniq: "\<lbrakk> is_inf x y i; is_inf x y i' \<rbrakk> \<Longrightarrow> i = i'"
    apply(simp add: is_inf_def)
    apply(simp add: anti_sym)
    done

    theorem sup_uniq: "\<lbrakk> is_sup x y s; is_sup x y s'\<rbrakk> \<Longrightarrow> s = s'"
    apply(simp add: is_sup_def)
    apply(simp add: anti_sym)
    done
    
  end 

(*extension of partial orders to lattices*)
locale lattice = partial_order + 
  assumes ex_inf: "\<exists>inf. is_inf x y inf"
    and ex_sup: "\<exists>sup. is_sup x y sup"
    begin
      
      (*THE: Definite description operator -
        denotes x such that P(x) \<rightarrow> T provided unique x*)
      definition meet (infixl "\<sqinter>" 70) where
        "x \<sqinter> y = (THE inf. is_inf x y inf)"

      definition join (infixl "\<squnion>" 65) where
        "x \<squnion> y = (THE sup. is_sup x y sup)"

      lemma meet_left:"x \<sqinter> y \<sqsubseteq> x"
      apply(simp add: meet_def)
      apply(simp add: is_inf_def)
      apply(rule theI)
      sorry
      
    end

locale total_order = partial_order +
  assumes total: "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"

lemma (in total_order) less_total: 
  "x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x"
using less_def total by auto


(*distributive lattice*)  
locale distrib_lattice = lattice +
  assumes meet_distr: "x \<sqinter> (y \<squnion> z) = x \<sqinter> y \<squnion> x \<sqinter> z"

lemma (in distrib_lattice) join_distr:
  "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
  apply(auto simp add: meet_distr meet_left)
  apply(simp add: join_def meet_def is_inf_def)
  apply(rule theI)
  sorry

(*sublocale x \<subseteq> y causes locale y to be interpreted in context of x
 conclusions of y are made available in x. Must prove that this is so*)
sublocale total_order \<subseteq> lattice
proof unfold_locales
(*since both extend lattices, only assumptions introduced in lattice remain as subgoals*)
fix x y
from total have "is_inf x y (if x \<sqsubseteq> y then x else y)"
  by (auto simp: is_inf_def)
then show "\<exists>inf. is_inf x y inf"
from total have "is_sup x y (if y \<sqsubseteq> x then y else x)"
  by (auto simp: is_sup_def)
then show "\<exists>sup. is_sup x y sup"
sorry

end