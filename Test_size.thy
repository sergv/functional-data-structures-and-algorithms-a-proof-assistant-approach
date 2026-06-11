theory Test_size
imports
  Main
  HOL.Num
  "HOL-Library.Tree"
begin

value "size (Node Leaf (1 :: nat) (Node Leaf 2 Leaf))"

datatype 'a List = Nil | Cons "'a" "'a List"

fun cons :: "'a \<Rightarrow> 'a List \<Rightarrow> 'a List"
where
  "cons x xs = Cons x xs"

fun append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List"
where
  "append Nil         ys = ys"
| "append (Cons x xs) ys = Cons x (append xs ys)"

value "size (cons 1 (cons 2 (cons (3 :: nat) Nil)))"

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

value "let (x, y) = (1, 2 :: int) in x + y"

value "(1 :: nat)"

thm List.list.rec

value "let x = [1, 2, 3 :: nat] in List.length x"

value "size [1, 2, 3 :: nat]"



end
