theory Leftist
imports
  Main
  HOL.Num
  "HOL-Library.Multiset"
  HOL.Transcendental
begin

value "size (Node Leaf 1 (Node Leaf 2 Leaf))"

datatype 'a List = Nil | Cons "'a" "'a List"

fun cons :: "'a \<Rightarrow> 'a List \<Rightarrow> 'a List"
where
  "cons x xs = Cons x xs"

fun append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List"
where
  "append Nil         ys = ys"
| "append (Cons x xs) ys = Cons x (append xs ys)"


lemma append_empty: "append xs Nil = xs"
proof (induct xs)
  case Nil
  then show ?case using append.simps by simp
next
  case (Cons x xs)
  then show ?case by simp
qed

thm append.cases
thm append.elims
thm append.induct
thm append.pelims
thm append.simps


thm List.rec
thm List.rec[no_vars]
print_theorems

section \<open>Trees\<close>

datatype 'a Tree =
  Leaf | (* ("\<langle>\<rangle>") | *)
  Node ("value": 'a) "'a Tree" "'a Tree" (* ("(1\<langle>_,/ _,/ _\<rangle>)") *)

primrec left :: "'a Tree \<Rightarrow> 'a Tree" where
"left (Node _ l _) = l" |
"left Leaf         = Leaf"

primrec right :: "'a Tree \<Rightarrow> 'a Tree" where
"right (Node _ _ r) = r" |
"right Leaf         = Leaf"


subsection \<open>Height\<close>

fun height :: "'a Tree => nat" where
"height Leaf         = 0" |
"height (Node _ l r) = max (height l) (height r) + 1"


fun mysize :: "'a Tree => nat" where
"mysize Leaf         = 0" |
"mysize (Node _ l r) = mysize l + mysize r + 1"

fun rank :: "'a Tree \<Rightarrow> nat" where
"rank Leaf = 0" |
"rank (Node _ l r) = min (rank l) (rank r) + 1"

thm rank.simps[no_vars]
thm rank.simps(1)
thm rank.simps(2)

(* Like in Okasaki’s book *)
fun rank_right :: "'a Tree \<Rightarrow> nat" where
"rank_right Leaf = 0" |
"rank_right (Node _ _ r) = rank_right r + 1"

thm rank_right.simps[no_vars]
thm rank_right.simps(1)
thm rank_right.simps(2)

fun leaf_count :: "'a Tree \<Rightarrow> nat" where
"leaf_count Leaf         = 1" |
"leaf_count (Node _ l r) = leaf_count l + leaf_count r"

lemma size_and_leaf_count2: "leaf_count t = mysize t + 1"
by (induction t) simp_all

lemma size_and_leaf_count: "leaf_count t = mysize t + 1"
proof (induction t)
  case Leaf
  then show ?case by simp
next
  case (Node _ l r)
  then show ?case by simp
qed



lemma times_two2:
  fixes a :: "nat"
  shows "2 * a = a + a"
proof -
  show "2 * a = a + a" using Num.semiring_numeral_class.mult_2[of a] .
qed

thm times_two2



lemma times_two:
  fixes a :: "nat"
  shows "2 * a = a + a"
  by auto

thm Num.semiring_numeral_class.mult_2

(*
lemma le_trans:
  fixes a b c
  assumes "a \<le> b"
  assumes "b \<le> c"
  shows "a \<le> c"
  by (auto simp add: order_trans)
*)

(*print_simpset*)

thm times_two[of "2 ^ rank l"]

thm trans


theorem size_and_rank:
  fixes t :: "'a Tree"
  shows "2 ^ rank t \<le> mysize t + 1"
proof (induction t)
  case Leaf
  thus "2 ^ rank Leaf \<le> mysize Leaf + 1"
  proof -
    have "rank Leaf \<equiv> 0" by (simp only: rank.simps(1))
    hence "2 ^ rank Leaf \<equiv> 1" by simp
    moreover have "mysize Leaf \<equiv> 0" by (simp only: mysize.simps(1))
    ultimately show ?thesis by simp
  qed
next
  case (Node x l r)

  have rank_expand: "rank (Node x l r) \<equiv> min (rank l) (rank r) + 1" by (simp only: rank.simps(2))

  have "min (rank l) (rank r) \<equiv> (if rank l \<le> rank r then rank l else rank r)" unfolding min_def .
  hence rank_expand2: "rank (Node x l r) \<equiv> (if rank l \<le> rank r then rank l else rank r) + 1" by (simp only: rank_expand)

  have size_expand: "mysize (Node x l r) \<equiv> mysize l + mysize r + 1" by (simp only: mysize.simps(2))

  thm rank_expand

  (* Show type of the local term *)
  term "2 * (2 ^ rank l)"

  thm Node.IH

  have ih_combined: "2 ^ rank l + 2 ^ rank r \<le> mysize l + mysize r + 1 + 1" using Node.IH by simp

  have expanded_le: "2 ^ ((if rank l \<le> rank r then rank l else rank r) + 1) \<le> mysize l + mysize r + 1 + 1"
  proof cases
    assume l_lt_r: "rank l \<le> rank r"

    hence 1: "if rank l \<le> rank r then rank l else rank r \<equiv> rank l" by simp

    have 2: "2 ^ (rank l + 1) \<equiv> 2 * (2 ^ rank l)" by simp

    have 3: "2 * (2 ^ rank l) :: nat \<equiv> 2 ^ rank l + 2 ^ rank l" by (simp only: times_two)

    have 4: "2 ^ rank l + (2 ^ rank l :: nat) \<le> 2 ^ rank l + 2 ^ rank r" using l_lt_r by auto

    thm order_trans[of "2 ^ rank l + (2 ^ rank l :: nat)" "2 ^ rank l + (2 ^ rank r :: nat)" "mysize l + mysize r + 1 + 1"]
    thm ih_combined

    hence 5: "2 ^ rank l + (2 ^ rank l :: nat) \<le> mysize l + mysize r + 1 + 1" using 4 ih_combined order_trans[of "2 ^ rank l + (2 ^ rank l :: nat)" "2 ^ rank l + (2 ^ rank r :: nat)" "mysize l + mysize r + 1 + 1"] by simp

    then show ?thesis using 1 2 3 4 5 by auto
  next
    (* Copypasta warning! *)
    assume not_l_le_r: "\<not> (rank l \<le> rank r)"
    hence l_ge_r: "rank l > rank r" by auto

    have 1: "if rank l \<le> rank r then rank l else rank r \<equiv> rank r" using not_l_le_r by auto

    have 2: "2 ^ (rank r + 1) \<equiv> 2 * (2 ^ rank r)" by simp

    have 3: "2 * (2 ^ rank r) :: nat \<equiv> 2 ^ rank r + 2 ^ rank r" by (simp only: times_two)

    have 4: "2 ^ rank r + (2 ^ rank r :: nat) \<le> 2 ^ rank l + 2 ^ rank r" using l_ge_r by auto

    hence 5: "2 ^ rank r + (2 ^ rank r :: nat) \<le> mysize l + mysize r + 1 + 1" using 4 ih_combined order_trans[of "2 ^ rank r + (2 ^ rank r :: nat)" "2 ^ rank l + (2 ^ rank r :: nat)" "mysize l + mysize r + 1 + 1"] by simp

    then show ?thesis using 1 2 3 4 5 by auto
  qed

  thm rank_expand2[symmetric]

  (* Glue it all together *)
  show ?case (*using expanded_le rank_expand2 size_expand *)
  proof -
    from expanded_le have "2 ^ ((if rank l \<le> rank r then rank l else rank r) + 1) \<le> mysize l + mysize r + 1 + 1" by simp
    hence "2 ^ rank (Node x l r) \<le> mysize l + mysize r + 1 + 1" by (simp only: rank_expand2)
    thus "2 ^ rank (Node x l r) \<le> mysize (Node x l r) + 1" by (simp only: size_expand)
  qed
qed


subsection \<open>Elements\<close>

primrec tree_elems :: "'a Tree \<Rightarrow> 'a set" where
"tree_elems Leaf         = {}" |
"tree_elems (Node x l r) = {x} \<union> tree_elems l \<union> tree_elems r"

primrec tree_multielems :: "'a Tree \<Rightarrow> 'a multiset" where
"tree_multielems Leaf         = {#}" |
"tree_multielems (Node x l r) = {# x #} + tree_multielems l + tree_multielems r"

subsection \<open>Heap\<close>

type_synonym 'a Leftist = "('a \<times> nat) Tree"

fun (in ord) is_heap :: "'a Tree \<Rightarrow> bool" where
"is_heap Leaf         = True" |
"is_heap (Node x l r) = ((\<forall> y \<in> (tree_elems l \<union> tree_elems r). x \<le> y) \<and> is_heap l \<and> is_heap r)"

fun is_leftist :: "'a Tree \<Rightarrow> bool" where
"is_leftist Leaf         = True" |
"is_leftist (Node _ l r) = (rank l \<ge> rank r \<and> is_leftist l \<and> is_leftist r)"

fun is_leftist_right :: "'a Tree \<Rightarrow> bool" where
"is_leftist_right Leaf         = True" |
"is_leftist_right (Node _ l r) = (rank_right l \<ge> rank_right r \<and> is_leftist_right l \<and> is_leftist_right r)"


subsection \<open>Formula for leftist heaps\<close>

thm Tree.induct

(* theorem "2\<^bsup>(rank (Node x l r))\<^esup> \<ge> 2 ^ rank r"
proof -
  oops

theorem "x\<^sub>y + 1 \<ge> x"
proof -
  oops

theorem "x\<^sup>y + 1 \<ge> x"
proof -
  oops

theorem "x\<^bsup>y + 1\<^esup> > x"
proof -
  oops *)

thm list.split
thm if_split

theorem size_and_rank_leftist:
  fixes t :: "'a Tree"
  assumes leftist_property: "is_leftist t"
  shows "2 ^ rank t \<le> mysize t + 1"
  using assms(1) (* put theorem assumptions into goal so that induction can affect them too *)
proof (induction t)
  case Leaf
  print_cases
  thm Leaf.prems
  from Leaf.prems show "2 ^ rank Leaf \<le> mysize Leaf + 1"
  proof -
    have "rank Leaf \<equiv> 0" by (simp only: rank.simps(1))
    hence "2 ^ rank Leaf \<equiv> 1" by simp
    moreover have "mysize Leaf \<equiv> 0" by (simp only: mysize.simps(1))
    ultimately show ?thesis by (simp)
  qed
next
  case (Node x l r)
  print_cases

  have rank_expand: "rank (Node x l r) \<equiv> min (rank l) (rank r) + 1" by (simp only: rank.simps(2))

  have "min (rank l) (rank r) \<equiv> (if rank l \<le> rank r then rank l else rank r)" unfolding min_def .
  hence rank_expand2: "rank (Node x l r) \<equiv> (if rank l \<le> rank r then rank l else rank r) + 1" by (simp only: rank_expand)

  thm is_leftist.simps

  have leftist_whole_node: "is_leftist (Node x l r)" using Node.prems by simp

  from leftist_whole_node have leftist_l: "is_leftist l" using is_leftist.simps by simp
  from leftist_whole_node have leftist_r: "is_leftist r" using is_leftist.simps by simp

  (* hence leftist_node: "rank r \<le> rank l" by simp *)
  from leftist_whole_node have leftist_node: "rank l \<ge> rank r" by simp
  hence rank_expand3: "rank (Node x l r) \<equiv> rank r + 1" using rank_expand2 by auto

  have size_expand: "mysize (Node x l r) \<equiv> mysize l + mysize r + 1" by (simp only: mysize.simps(2))

  thm rank_expand

  (* Show type of the local term *)
  term "2 * (2 ^ rank l)"

  thm Node.IH

  have ih_combined: "2 ^ rank l + 2 ^ rank r \<le> mysize l + mysize r + 1 + 1" using Node.IH leftist_l leftist_r by simp

  have expanded_le: "2 ^ ((if rank l \<le> rank r then rank l else rank r) + 1) \<le> mysize l + mysize r + 1 + 1"
  proof -
    have "(if rank l \<le> rank r then rank l else rank r) = rank r"
    proof cases
      assume eq: "rank l = rank r"
      then show ?thesis by auto
    next
      assume "\<not> (rank l = rank r)"
      show ?thesis using leftist_node by auto
    qed
    hence 1: "(if rank l \<le> rank r then rank l else rank r) \<equiv> rank r" by auto

    have 2: "2 ^ (rank r + 1) \<equiv> 2 * (2 ^ rank r)" by simp

    have 3: "2 * (2 ^ rank r) :: nat \<equiv> 2 ^ rank r + 2 ^ rank r" by (simp only: times_two)

    have 4: "2 ^ rank r + (2 ^ rank r :: nat) \<le> 2 ^ rank l + 2 ^ rank r" using leftist_node by auto

    hence 5: "2 ^ rank r + (2 ^ rank r :: nat) \<le> mysize l + mysize r + 1 + 1" using 4 ih_combined order_trans[of "2 ^ rank r + (2 ^ rank r :: nat)" "2 ^ rank l + (2 ^ rank r :: nat)" "mysize l + mysize r + 1 + 1"] by simp

    then show ?thesis using 1 2 3 4 5 by auto
  qed

  thm rank_expand2[symmetric]

  (* Glue it all together *)
  show "2 ^ rank (Node x l r) \<le> mysize (Node x l r) + 1" (*using expanded_le rank_expand2 size_expand *)
  proof -
    from expanded_le have "2 ^ ((if rank l \<le> rank r then rank l else rank r) + 1) \<le> mysize l + mysize r + 1 + 1" by simp
    hence "2 ^ rank (Node x l r) \<le> mysize l + mysize r + 1 + 1" by (simp only: rank_expand2)
    thus "2 ^ rank (Node x l r) \<le> mysize (Node x l r) + 1" by (simp only: size_expand)
  qed
qed

theorem size_and_rank_leftist_small:
  fixes t :: "'a Tree"
  assumes leftist_property: "is_leftist t"
  shows "2 ^ rank t \<le> mysize t + 1"
  using assms(1) (* put theorem assumptions into goal so that induction can affect them too *)
proof (induction t)
  case Leaf
  print_cases
  thm Leaf.prems
  from Leaf.prems show "2 ^ rank Leaf \<le> mysize Leaf + 1"
  proof -
    have "rank Leaf \<equiv> 0" by (simp only: rank.simps(1))
    hence "2 ^ rank Leaf \<equiv> 1" by simp
    moreover have "mysize Leaf \<equiv> 0" by (simp only: mysize.simps(1))
    ultimately show ?thesis by (simp)
  qed
next
  case (Node x l r)
  print_cases
  have leftist_node: "rank l \<ge> rank r" using Node.prems by simp

  have node_rank: "rank (Node x l r) \<equiv> rank r + 1" using leftist_node by auto
  have node_size: "mysize (Node x l r) \<equiv> mysize l + mysize r + 1" by (simp only: mysize.simps(2))

  have ih_combined: "2 ^ rank l + 2 ^ rank r \<le> mysize l + mysize r + 1 + 1" using Node.IH Node.prems by simp

  have expanded_le: "2 ^ (min (rank l) (rank r) + 1) \<le> mysize l + mysize r + 1 + 1"
  proof -
    have 1: "min (rank l) (rank r) = rank r" using leftist_node by auto

    have 2: "2 ^ (rank r + 1) = 2 * (2 ^ rank r)" by simp

    have 3: "(2 :: nat) * (2 ^ rank r) = 2 ^ rank r + 2 ^ rank r" by (simp only: times_two)

    have 4: "2 ^ rank r + (2 ^ rank r :: nat) \<le> 2 ^ rank l + 2 ^ rank r" using leftist_node by auto

    note order = order_trans[of "2 ^ rank r + (2 ^ rank r :: nat)" "2 ^ rank l + (2 ^ rank r :: nat)" "mysize l + mysize r + 1 + 1"]
    thm order

    hence 5: "2 ^ rank r + (2 ^ rank r :: nat) \<le> mysize l + mysize r + 1 + 1" using 4 ih_combined order by simp

    then show ?thesis using 1 2 3 4 by simp
  qed

  (* Glue it all together *)
  show "2 ^ rank (Node x l r) \<le> mysize (Node x l r) + 1"
  proof -
    from expanded_le have "2 ^ rank (Node x l r) \<le> mysize l + mysize r + 1 + 1" using leftist_node node_rank by auto
    thus "2 ^ rank (Node x l r) \<le> mysize (Node x l r) + 1" by (simp only: node_size)
  qed
qed

lemma transitive_ordering:
  fixes x :: "nat"
  fixes y z
  assumes "x \<le> y"
  assumes "y \<le> z"
  shows "x \<le> z"
proof -
  show ?thesis using order_trans[of "x" "y" "z"] assms by auto
qed


theorem size_and_rank_leftist_small_small:
  fixes t :: "'a Tree"
  assumes leftist_property: "is_leftist t"
  shows "2 ^ rank t \<le> mysize t + 1"
  using assms(1) (* put theorem assumptions into goal so that induction can affect them too *)
proof (induction t)
  case Leaf
  print_cases
  thm Leaf.prems
  from Leaf.prems show "2 ^ rank Leaf \<le> mysize Leaf + 1"
  proof -
    have "rank Leaf \<equiv> 0" by (simp only: rank.simps(1))
    hence "2 ^ rank Leaf \<equiv> 1" by simp
    moreover have "mysize Leaf \<equiv> 0" by (simp only: mysize.simps(1))
    ultimately show ?thesis by (simp)
  qed
next
  case (Node x l r)
  print_cases
  have leftist_node: "rank l \<ge> rank r" using Node.prems by simp

  have node_rank: "rank (Node x l r) \<equiv> rank r + 1" using leftist_node by auto
  have node_size: "mysize (Node x l r) \<equiv> mysize l + mysize r + 1" by (simp only: mysize.simps(2))
  have ih_combined: "2 ^ rank l + 2 ^ rank r \<le> mysize l + mysize r + 1 + 1" using Node.IH Node.prems by simp

  show "2 ^ rank (Node x l r) \<le> mysize (Node x l r) + 1"
    apply (simp only: node_rank node_size)
  proof -
    have "2 ^ (rank r + 1) = 2 * (2 ^ rank r)" by simp
    hence 1: "... = 2 ^ rank r + (2 ^ rank r :: nat)" using times_two by auto

    have 2: "2 ^ rank r + 2 ^ rank r \<le> 2 ^ rank l + (2 ^ rank r :: nat)" using leftist_node by auto

    note order = order_trans[of "2 ^ (rank r + 1)" "2 ^ rank l + (2 ^ rank r :: nat)" "mysize l + mysize r + 1 + 1"]
    thm order_trans
    thm order

    from 1 2 have "2 ^ (rank r + 1) \<le> 2 ^ rank l + (2 ^ rank r :: nat)" by simp
    thus "2 ^ (rank r + 1) \<le> mysize l + mysize r + 1 + 1" using ih_combined order leftist_node by auto
  qed
qed

theorem size_and_rank_leftist_right:
  fixes t :: "'a Tree"
  assumes leftist_property: "is_leftist_right t"
  shows "2 ^ rank_right t \<le> mysize t + 1"
  using assms(1) (* put theorem assumptions into goal so that induction can affect them too *)
proof (induction t)
  case Leaf
  print_cases
  thm Leaf.prems
  from Leaf.prems show "2 ^ rank_right Leaf \<le> mysize Leaf + 1"
  proof -
    have "rank_right Leaf \<equiv> 0" by (simp only: rank_right.simps(1))
    hence "2 ^ rank_right Leaf \<equiv> 1" by simp
    moreover have "mysize Leaf \<equiv> 0" by (simp only: mysize.simps(1))
    ultimately show ?thesis by (simp)
  qed
next
  case (Node x l r)
  print_cases
  have leftist_node: "rank_right l \<ge> rank_right r" using Node.prems by simp

  have node_rank: "rank_right (Node x l r) \<equiv> rank_right r + 1" using leftist_node by auto
  have node_size: "mysize (Node x l r) \<equiv> mysize l + mysize r + 1" by (simp only: mysize.simps(2))
  have ih_combined: "2 ^ rank_right l + 2 ^ rank_right r \<le> mysize l + mysize r + 1 + 1" using Node.IH Node.prems by simp

  show "2 ^ rank_right (Node x l r) \<le> mysize (Node x l r) + 1"
    apply (simp only: node_rank node_size)
  proof -
    have "2 ^ (rank_right r + 1) = 2 * (2 ^ rank_right r)" by simp
    hence 1: "... = 2 ^ rank_right r + (2 ^ rank_right r :: nat)" using times_two by auto

    have 2: "2 ^ rank_right r + 2 ^ rank_right r \<le> 2 ^ rank_right l + (2 ^ rank_right r :: nat)" using leftist_node by auto

    note order = order_trans[of "2 ^ (rank_right r + 1)" "2 ^ rank_right l + (2 ^ rank_right r :: nat)" "mysize l + mysize r + 1 + 1"]
    thm order_trans
    thm order

    from 1 2 have "2 ^ (rank_right r + 1) \<le> 2 ^ rank_right l + (2 ^ rank_right r :: nat)" by simp
    thus "2 ^ (rank_right r + 1) \<le> mysize l + mysize r + 1 + 1" using ih_combined order leftist_node by auto
  qed
qed

thm log_powr_cancel [of "2" "rank_right t"]
term "2 powr 2 :: real"

lemma suc_real:
  fixes x :: "nat"
  shows "real x + 1 = real (Suc x)"
proof (induction x)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then show ?case by auto
qed

lemma to_powr:
  fixes x :: "nat"
  shows "2 ^ x = 2 powr (real x)"
proof (induction x)
  case 0
  then show ?case by auto
next
  case (Suc x)

  print_cases

  thm Suc.IH

  have 1: "2 ^ (x + 1) = 2 * 2 ^ x" by auto

  thm powr_mult_base[of "2" "real x"]

  have "2 powr (1 + real x) = 2 * 2 powr (real x)" using powr_mult_base by auto
  hence 2: "2 powr (real x + 1) = 2 * 2 powr (real x)" by (simp add: algebra_simps)

  from Suc.IH have "2 ^ x = 2 powr (real x)" by auto
  hence "2 * 2 ^ x = 2 * 2 powr (real x)" by auto
  hence "2 ^ (x + 1) = 2 * 2 powr (real x)" using 1 by auto
  hence "2 ^ (x + 1) = 2 powr (real x + 1)" using 2 by auto
  hence "2 ^ (Suc x) = 2 powr (real x + 1)" by auto
  thus "2 ^ (Suc x) = 2 powr (real (Suc x))" using suc_real by auto
qed

theorem size_and_rank_leftist_right_exercise:
  fixes t :: "'a Tree"
  assumes leftist_property: "is_leftist_right t"
  shows "real (rank_right t) \<le> log 2 (real (mysize t) + 1)"
proof -
  have "2 ^ rank_right t \<le> mysize t + 1" using size_and_rank_leftist_right leftist_property by auto
  hence "real (2 ^ rank_right t) \<le> real (mysize t + 1)" using of_nat_mono[of "2 ^ rank_right t" "mysize t + 1"] by auto
  hence "2 powr (real (rank_right t)) \<le> real (mysize t) + 1" using to_powr by auto

  hence "log 2 (2 powr (real (rank_right t))) \<le> log 2 (real (mysize t) + 1)"
    using log_mono[of "2" "2 powr (real (rank_right t))"] by auto

  hence "real (rank_right t) \<le> log 2 (real (mysize t) + 1)" by auto

  thus ?thesis by auto
qed

lemma alternative_rank_defs_prelim:
  fixes t :: "'a Tree"
  assumes "is_leftist t"
  assumes "is_leftist_right t"
  shows "rank t = rank_right t"
  using assms(1)
proof (induction t)
  case Leaf
  show ?case sorry
next
  case (Node x l r)
  print_cases
  show ?case sorry
qed

lemma alternative_rank_defs:
  fixes t :: "'a Tree"
  assumes "is_leftist t"
  assumes "is_leftist_right t"
  shows "rank t = rank_right t"
  using assms(1)
proof (induction t)
  case Leaf
  show ?case by simp
next
  case (Node x l r)
  print_cases
  show ?case using Node.IH Node.prems by auto
qed

subsection \<open>Misc\<close>


fun rank_cached :: "'a Leftist \<Rightarrow> nat" where
"rank_cached Leaf = 0" |
"rank_cached (Node (_, n) _ _) = n"

(*
fun is_leftist :: "'a Leftist \<Rightarrow> bool" where
"is_leftist Leaf              = True" |
"is_leftist (Node (x, n) l r) =
*)


(*
section \<open>Finite sequences\<close>

theory Seq
  imports Main
begin

datatype 'a seq = Empty | Seq 'a "'a seq"

fun conc :: "'a seq \<Rightarrow> 'a seq \<Rightarrow> 'a seq"
where
  "conc Empty ys = ys"
| "conc (Seq x xs) ys = Seq x (conc xs ys)"

fun reverse :: "'a seq \<Rightarrow> 'a seq"
where
  "reverse Empty = Empty"
| "reverse (Seq x xs) = conc (reverse xs) (Seq x Empty)"

lemma conc_empty: "conc xs Empty = xs"
  by (induct xs) simp_all

lemma conc_assoc: "conc (conc xs ys) zs = conc xs (conc ys zs)"
  by (induct xs) simp_all

lemma reverse_conc: "reverse (conc xs ys) = conc (reverse ys) (reverse xs)"
  by (induct xs) (simp_all add: conc_empty conc_assoc)

lemma reverse_reverse: "reverse (reverse xs) = xs"
  by (induct xs) (simp_all add: reverse_conc)

end

*)

(*
value "let (x, y) = (1, 2 :: int) in x + y"

value "(1 :: nat)"

thm List.list.rec

value "let x = [1, 2, 3 :: nat] in List.length x"

value "size [1, 2, 3 :: nat]"

*)


end
