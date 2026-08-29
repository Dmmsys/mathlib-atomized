/-
Copyright (c) 2021 Chris Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Bailey
-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.String.Defs

/-!
# Miscellaneous lemmas about strings
-/

public section

namespace String

/--
lemma `congr_append` / 引理 `congr_append`

English:
lemma congr_append
  given: (a b : String)
  statement: a ++ b = String.ofList (a.toList ++ b.toList)
  proof: by simp

中文:
引理 congr_append
  条件: (a b : String)
  结论: a ++ b = String.ofList (a.toList ++ b.toList)
  证明: by simp
-/
lemma congr_append (a b : String) : a ++ b = String.ofList (a.toList ++ b.toList) := by simp

/--
lemma `length_replicate` / 引理 `length_replicate`

English:
lemma length_replicate
  given: (n : Nat) (c : Char)
  statement: (replicate n c).length = n
  proof: by
  simp only [← length_toList, String.replicate, String.toList_ofList, List.length_replicate]

中文:
引理 length_replicate
  条件: (n : 自然数) (c : Char)
  结论: (replicate n c).length = n
  证明: by
  simp only [← length_toList, String.replicate, String.toList_ofList, List.length_replicate]
-/
@[simp] lemma length_replicate (n : Nat) (c : Char) : (replicate n c).length = n := by
  simp only [← length_toList, String.replicate, String.toList_ofList, List.length_replicate]

/--
lemma `length_eq_list_length` / 引理 `length_eq_list_length`

English:
lemma length_eq_list_length
  given: (l : List Char)
  statement: (String.ofList l).length = l.length
  proof: by
  simp

中文:
引理 length_eq_list_length
  条件: (l : List Char)
  结论: (String.ofList l).length = l.length
  证明: by
  simp
-/
lemma length_eq_list_length (l : List Char) : (String.ofList l).length = l.length := by
  simp

/--
lemma `length_leftpad` / 引理 `length_leftpad`

English:
lemma length_leftpad
  given: (n : Nat) (c : Char)

中文:
引理 length_leftpad
  条件: (n : 自然数) (c : Char)
-/
@[simp] lemma length_leftpad (n : Nat) (c : Char) :
    forall (s : String), (leftpad n c s).length = max n s.length
  | s => by simp [leftpad, length_toList, Nat.sub_add_eq_max]

/--
lemma `leftpad_prefix` / 引理 `leftpad_prefix`

English:
lemma leftpad_prefix
  given: (n : Nat) (c : Char)
  statement: forall s, IsPrefix (replicate (n - length s) c) (leftpad n c s)

中文:
引理 leftpad_prefix
  条件: (n : 自然数) (c : Char)
  结论: 对任意 s, IsPrefix (replicate (n - length s) c) (leftpad n c s)
-/
lemma leftpad_prefix (n : Nat) (c : Char) : forall s, IsPrefix (replicate (n - length s) c) (leftpad n c s)
  | s => by simp [leftpad, IsPrefix, replicate, length_toList]

/--
lemma `leftpad_suffix` / 引理 `leftpad_suffix`

English:
lemma leftpad_suffix
  given: (n : Nat) (c : Char)
  statement: forall s, IsSuffix s (leftpad n c s)

中文:
引理 leftpad_suffix
  条件: (n : 自然数) (c : Char)
  结论: 对任意 s, IsSuffix s (leftpad n c s)
-/
lemma leftpad_suffix (n : Nat) (c : Char) : forall s, IsSuffix s (leftpad n c s)
  | s => by simp [leftpad, IsSuffix]

end String
