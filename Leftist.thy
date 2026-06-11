theory Leftist
imports
  Main
  HOL.Num
  "HOL-Library.Multiset"
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

thm rank.simps(1)
thm rank.simps(2)



fun leaf_count :: "'a Tree \<Rightarrow> nat" where
"leaf_count Leaf         = 1" |
"leaf_count (Node _ l r) = leaf_count l + leaf_count r"


lemma size_and_leaf_count: "leaf_count t = mysize t + 1"
(*by (induction t) simp_all*)
proof (induction t)
  case Leaf
  then show ?case by simp
next
  case (Node _ l r)
  then show ?case by simp
qed


(*
lemma times_two2:
  fixes a :: "semiring_numeral"
  shows "2 * a = a + a"
  using Num.semiring_numeral_class.mult_2 by auto
qed

thm times_two2
*)


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

  have ih_combined: "2 ^ rank l + 2 ^ rank r \<le> mysize l + mysize r + 1 + 1" using Node.IH by simp

  have expanded_le: "2 ^ ((if rank l \<le> rank r then rank l else rank r) + 1) \<le> mysize l + mysize r + 1 + 1"
  proof cases
    assume l_lt_r: "rank l \<le> rank r"

    hence 1: "if rank l \<le> rank r then rank l else rank r \<equiv> rank l" by simp

    have 2: "2 ^ (rank l + 1) \<equiv> 2 * (2 ^ rank l)" by simp

    have 3: "2 * (2 ^ rank l) :: nat \<equiv> 2 ^ rank l + 2 ^ rank l" by (simp only: times_two)

    have 4: "2 ^ rank l + (2 ^ rank l :: nat) \<le> 2 ^ rank l + 2 ^ rank r" using l_lt_r by auto

    hence 5: "2 ^ rank l + (2 ^ rank l :: nat) \<le> mysize l + mysize r + 1 + 1" using 4 ih_combined order_trans[of "2 ^ rank l + (2 ^ rank l :: nat)" "2 ^ rank l + (2 ^ rank r :: nat)"] by auto

    then show ?thesis using 1 2 3 4 5 by auto
  next
    (* Copypasta warning! *)
    assume not_l_le_r: "\<not> (rank l \<le> rank r)"
    hence l_ge_r: "rank l > rank r" by auto

    have 1: "if rank l \<le> rank r then rank l else rank r \<equiv> rank r" using not_l_le_r by auto

    have 2: "2 ^ (rank r + 1) \<equiv> 2 * (2 ^ rank r)" by simp

    have 3: "2 * (2 ^ rank r) :: nat \<equiv> 2 ^ rank r + 2 ^ rank r" by (simp only: times_two)

    have 4: "2 ^ rank r + (2 ^ rank r :: nat) \<le> 2 ^ rank l + 2 ^ rank r" using l_ge_r by auto

    hence 5: "2 ^ rank r + (2 ^ rank r :: nat) \<le> mysize l + mysize r + 1 + 1" using 4 ih_combined order_trans[of "2 ^ rank r + (2 ^ rank r :: nat)" "2 ^ rank l + (2 ^ rank r :: nat)"] by auto

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
"is_heap (Node x l r) = ((\<forall> y \<in> tree_elems l \<union> tree_elems r. x \<le> y) \<and> is_heap l \<and> is_heap r)"





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
