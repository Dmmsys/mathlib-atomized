/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Data.Nat.Notation

/-!
# Iterations of a function

In this file we prove simple properties of `Nat.iterate f n` a.k.a. `f^[n]`:

* `iterate_zero`, `iterate_succ`, `iterate_succ'`, `iterate_add`, `iterate_mul`:
  formulas for `f^[0]`, `f^[n+1]` (two versions), `f^[n+m]`, and `f^[n*m]`;

* `iterate_id` : `id^[n]=id`;

* `Injective.iterate`, `Surjective.iterate`, `Bijective.iterate` :
  iterates of an injective/surjective/bijective function belong to the same class;

* `LeftInverse.iterate`, `RightInverse.iterate`, `Commute.iterate_left`, `Commute.iterate_right`,
  `Commute.iterate_iterate`:
  some properties of pairs of functions survive under iterations

* `iterate_fixed`, `Function.Semiconj.iterate_*`, `Function.Semiconj₂.iterate`:
  if `f` fixes a point (resp., semiconjugates unary/binary operations), then so does `f^[n]`.

-/

@[expose] public section


universe u v

variable {α : Type u} {β : Type v}

/--
Definition of `Nat.iterate` / `Nat.iterate` 的定义

English:
definition Nat.iterate
  signature: {α : Sort u} (op : α -> α)

中文:
定义 自然数.iterate
  签名: {α : 类型层 u} (op : α -> α)
-/
def Nat.iterate {α : Sort u} (op : α -> α) : Nat -> α -> α
  | 0, a => a
  | succ k, a => iterate op k (op a)

@[inherit_doc Nat.iterate]
notation:max f "^[" n "]" => Nat.iterate f n

namespace Function

open Function (Commute)

variable (f : α -> α)

@[simp]
/--
theorem `iterate_zero` / 定理 `iterate_zero`

English:
theorem iterate_zero
  statement: f^[0] = id
  proof: rfl

中文:
定理 iterate_zero
  结论: f^[0] = id
  证明: rfl
-/
theorem iterate_zero : f^[0] = id :=
  rfl

/--
theorem `iterate_zero_apply` / 定理 `iterate_zero_apply`

English:
theorem iterate_zero_apply
  given: (x : α)
  statement: f^[0] x = x
  proof: rfl

@[simp]

中文:
定理 iterate_zero_apply
  条件: (x : α)
  结论: f^[0] x = x
  证明: rfl

@[simp]
-/
theorem iterate_zero_apply (x : α) : f^[0] x = x :=
  rfl

@[simp]
/--
theorem `iterate_succ` / 定理 `iterate_succ`

English:
theorem iterate_succ
  given: (n : Nat)
  statement: f^[n.succ] = f^[n] ∘ f
  proof: rfl

中文:
定理 iterate_succ
  条件: (n : 自然数)
  结论: f^[n.succ] = f^[n] ∘ f
  证明: rfl
-/
theorem iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f :=
  rfl

/--
theorem `iterate_succ_apply` / 定理 `iterate_succ_apply`

English:
theorem iterate_succ_apply
  given: (n : Nat) (x : α)
  statement: f^[n.succ] x = f^[n] (f x)
  proof: rfl

@[simp]

中文:
定理 iterate_succ_apply
  条件: (n : 自然数) (x : α)
  结论: f^[n.succ] x = f^[n] (f x)
  证明: rfl

@[simp]
-/
theorem iterate_succ_apply (n : Nat) (x : α) : f^[n.succ] x = f^[n] (f x) :=
  rfl

@[simp]
/--
theorem `iterate_id` / 定理 `iterate_id`

English:
theorem iterate_id
  given: (n : Nat)
  statement: (id : α -> α)^[n] = id
  proof: Nat.recOn n rfl fun n ihn => by rw [iterate_succ, ihn, id_comp]

中文:
定理 iterate_id
  条件: (n : 自然数)
  结论: (id : α -> α)^[n] = id
  证明: Nat.recOn n rfl fun n ihn => by rw [iterate_succ, ihn, id_comp]

Depends on / 依赖: Nat.recOn, id_comp, iterate_succ
-/
theorem iterate_id (n : Nat) : (id : α -> α)^[n] = id :=
  Nat.recOn n rfl fun n ihn => by rw [iterate_succ, ihn, id_comp]

/--
theorem `iterate_add` / 定理 `iterate_add`

English:
theorem iterate_add
  given: (m : Nat)
  statement: forall n : Nat, f^[m + n] = f^[m] ∘ f^[n]

中文:
定理 iterate_add
  条件: (m : 自然数)
  结论: 对任意 n : 自然数, f^[m + n] = f^[m] ∘ f^[n]
-/
theorem iterate_add (m : Nat) : forall n : Nat, f^[m + n] = f^[m] ∘ f^[n]
  | 0 => rfl
  | Nat.succ n => by rw [Nat.add_succ, iterate_succ, iterate_succ, iterate_add m n]; rfl

/--
theorem `iterate_add_apply` / 定理 `iterate_add_apply`

English:
theorem iterate_add_apply
  given: (m n : Nat) (x : α)
  statement: f^[m + n] x = f^[m] (f^[n] x)
  proof: by
  rw [iterate_add f m n]
  rfl

中文:
定理 iterate_add_apply
  条件: (m n : 自然数) (x : α)
  结论: f^[m + n] x = f^[m] (f^[n] x)
  证明: by
  rw [iterate_add f m n]
  rfl

Depends on / 依赖: iterate_add
-/
theorem iterate_add_apply (m n : Nat) (x : α) : f^[m + n] x = f^[m] (f^[n] x) := by
  rw [iterate_add f m n]
  rfl

-- can be proved by simp but this is shorter and more natural
@[simp high]
/--
theorem `iterate_one` / 定理 `iterate_one`

English:
theorem iterate_one
  statement: f^[1] = f
  proof: funext fun _ => rfl

中文:
定理 iterate_one
  结论: f^[1] = f
  证明: funext fun _ => rfl
-/
theorem iterate_one : f^[1] = f :=
  funext fun _ => rfl

/--
theorem `iterate_mul` / 定理 `iterate_mul`

English:
theorem iterate_mul
  given: (m : Nat)
  statement: forall n, f^[m * n] = f^[m]^[n]

中文:
定理 iterate_mul
  条件: (m : 自然数)
  结论: 对任意 n, f^[m * n] = f^[m]^[n]
-/
theorem iterate_mul (m : Nat) : forall n, f^[m * n] = f^[m]^[n]
  | 0 => by simp only [Nat.mul_zero, iterate_zero]
  | n + 1 => by simp only [Nat.mul_succ, iterate_one, iterate_add, iterate_mul m n]

variable {f}

/--
theorem `iterate_fixed` / 定理 `iterate_fixed`

English:
theorem iterate_fixed
  given: {x} (h : f x = x) (n : Nat)
  statement: f^[n] x = x
  proof: Nat.recOn n rfl fun n ihn => by rw [iterate_succ_apply, h, ihn]

中文:
定理 iterate_fixed
  条件: {x} (h : f x = x) (n : 自然数)
  结论: f^[n] x = x
  证明: Nat.recOn n rfl fun n ihn => by rw [iterate_succ_apply, h, ihn]

Depends on / 依赖: Nat.recOn, iterate_succ_apply
-/
theorem iterate_fixed {x} (h : f x = x) (n : Nat) : f^[n] x = x :=
  Nat.recOn n rfl fun n ihn => by rw [iterate_succ_apply, h, ihn]

/--
theorem `iterate_invariant` / 定理 `iterate_invariant`

English:
theorem iterate_invariant
  given: {g : α -> β} (h : g ∘ f = g) (n : Nat)
  statement: g ∘ f^[n] = g
  proof: match n with
  | 0 => by rw [iterate_zero, comp_id]
  | m + 1 => by rwa [iterate_succ, ← comp_assoc, iterate_invariant h m]

中文:
定理 iterate_invariant
  条件: {g : α -> β} (h : g ∘ f = g) (n : 自然数)
  结论: g ∘ f^[n] = g
  证明: match n with
  | 0 => by rw [iterate_zero, comp_id]
  | m + 1 => by rwa [iterate_succ, ← comp_assoc, iterate_invariant h m]
-/
theorem iterate_invariant {g : α -> β} (h : g ∘ f = g) (n : Nat) : g ∘ f^[n] = g := match n with
  | 0 => by rw [iterate_zero, comp_id]
  | m + 1 => by rwa [iterate_succ, ← comp_assoc, iterate_invariant h m]

/--
theorem `Injective.iterate` / 定理 `Injective.iterate`

English:
theorem Injective.iterate
  given: (Hinj : Injective f) (n : Nat)
  statement: Injective f^[n]
  proof: Nat.recOn n injective_id fun _ ihn => ihn.comp Hinj

中文:
定理 单射.iterate
  条件: (Hinj : 单射 f) (n : 自然数)
  结论: 单射 f^[n]
  证明: Nat.recOn n injective_id fun _ ihn => ihn.comp Hinj

Depends on / 依赖: Nat.recOn, ihn.comp, injective_id
-/
theorem Injective.iterate (Hinj : Injective f) (n : Nat) : Injective f^[n] :=
  Nat.recOn n injective_id fun _ ihn => ihn.comp Hinj

/--
theorem `Surjective.iterate` / 定理 `Surjective.iterate`

English:
theorem Surjective.iterate
  given: (Hsurj : Surjective f) (n : Nat)
  statement: Surjective f^[n]
  proof: Nat.recOn n surjective_id fun _ ihn => ihn.comp Hsurj

中文:
定理 满射.iterate
  条件: (Hsurj : 满射 f) (n : 自然数)
  结论: 满射 f^[n]
  证明: Nat.recOn n surjective_id fun _ ihn => ihn.comp Hsurj

Depends on / 依赖: Nat.recOn, ihn.comp, surjective_id
-/
theorem Surjective.iterate (Hsurj : Surjective f) (n : Nat) : Surjective f^[n] :=
  Nat.recOn n surjective_id fun _ ihn => ihn.comp Hsurj

/--
theorem `Bijective.iterate` / 定理 `Bijective.iterate`

English:
theorem Bijective.iterate
  given: (Hbij : Bijective f) (n : Nat)
  statement: Bijective f^[n]
  proof: ⟨Hbij.1.iterate n, Hbij.2.iterate n⟩

中文:
定理 双射.iterate
  条件: (Hbij : 双射 f) (n : 自然数)
  结论: 双射 f^[n]
  证明: ⟨Hbij.1.iterate n, Hbij.2.iterate n⟩

Depends on / 依赖: iterate
-/
theorem Bijective.iterate (Hbij : Bijective f) (n : Nat) : Bijective f^[n] :=
  ⟨Hbij.1.iterate n, Hbij.2.iterate n⟩

namespace Semiconj

/--
theorem `iterate_right` / 定理 `iterate_right`

English:
theorem iterate_right
  given: {f : α -> β} {ga : α -> α} {gb : β -> β} (h : Semiconj f ga gb) (n : Nat)
  proof: Nat.recOn n id_right fun _ ihn => ihn.comp_right h

中文:
定理 iterate_right
  条件: {f : α -> β} {ga : α -> α} {gb : β -> β} (h : Semiconj f ga gb) (n : 自然数)
  证明: Nat.recOn n id_right fun _ ihn => ihn.comp_right h

Depends on / 依赖: Nat.recOn, comp_right, id_right, ihn.comp_right
-/
theorem iterate_right {f : α -> β} {ga : α -> α} {gb : β -> β} (h : Semiconj f ga gb) (n : Nat) :
    Semiconj f ga^[n] gb^[n] :=
  Nat.recOn n id_right fun _ ihn => ihn.comp_right h

/--
theorem `iterate_left` / 定理 `iterate_left`

English:
theorem iterate_left
  given: {g : Nat -> α -> α} (H : forall n, Semiconj f (g n) (g <| n + 1)) (n k : Nat)
  proof: by
  induction n generalizing k with
  | zero =>
    rw [Nat.zero_add]
    exact id_left
  | succ n ihn =>
    rw [Nat.add_right_comm]; rw [Nat.add_assoc]
    exact (H k).trans (ihn (k + 1))

中文:
定理 iterate_left
  条件: {g : 自然数 -> α -> α} (H : 对任意 n, Semiconj f (g n) (g <| n + 1)) (n k : 自然数)
  证明: by
  induction n generalizing k with
  | zero =>
    rw [Nat.zero_add]
    exact id_left
  | succ n ihn =>
    rw [Nat.add_right_comm]; rw [Nat.add_assoc]
    exact (H k).trans (ihn (k + 1))

Depends on / 依赖: Nat.add_assoc, Nat.add_right_comm, Nat.zero_add, add_assoc, add_right_comm, generalizing, id_left, zero_add
-/
theorem iterate_left {g : Nat -> α -> α} (H : forall n, Semiconj f (g n) (g <| n + 1)) (n k : Nat) :
    Semiconj f^[n] (g k) (g <| n + k) := by
  induction n generalizing k with
  | zero =>
    rw [Nat.zero_add]
    exact id_left
  | succ n ihn =>
    rw [Nat.add_right_comm]; rw [Nat.add_assoc]
    exact (H k).trans (ihn (k + 1))

end Semiconj

namespace Commute

variable {g : α -> α}

/--
theorem `iterate_right` / 定理 `iterate_right`

English:
theorem iterate_right
  given: (h : Commute f g) (n : Nat)
  statement: Commute f g^[n]
  proof: Semiconj.iterate_right h n

中文:
定理 iterate_right
  条件: (h : Commute f g) (n : 自然数)
  结论: Commute f g^[n]
  证明: Semiconj.iterate_right h n

Depends on / 依赖: Semiconj, Semiconj.iterate_right, iterate_right
-/
theorem iterate_right (h : Commute f g) (n : Nat) : Commute f g^[n] :=
  Semiconj.iterate_right h n

/--
theorem `iterate_left` / 定理 `iterate_left`

English:
theorem iterate_left
  given: (h : Commute f g) (n : Nat)
  statement: Commute f^[n] g
  proof: (h.symm.iterate_right n).symm

中文:
定理 iterate_left
  条件: (h : Commute f g) (n : 自然数)
  结论: Commute f^[n] g
  证明: (h.symm.iterate_right n).symm

Depends on / 依赖: h.symm.iterate_right, iterate_right
-/
theorem iterate_left (h : Commute f g) (n : Nat) : Commute f^[n] g :=
  (h.symm.iterate_right n).symm

/--
theorem `iterate_iterate` / 定理 `iterate_iterate`

English:
theorem iterate_iterate
  given: (h : Commute f g) (m n : Nat)
  statement: Commute f^[m] g^[n]
  proof: (h.iterate_left m).iterate_right n

中文:
定理 iterate_iterate
  条件: (h : Commute f g) (m n : 自然数)
  结论: Commute f^[m] g^[n]
  证明: (h.iterate_left m).iterate_right n

Depends on / 依赖: h.iterate_left, iterate_left, iterate_right
-/
theorem iterate_iterate (h : Commute f g) (m n : Nat) : Commute f^[m] g^[n] :=
  (h.iterate_left m).iterate_right n

/--
theorem `iterate_eq_of_map_eq` / 定理 `iterate_eq_of_map_eq`

English:
theorem iterate_eq_of_map_eq
  given: (h : Commute f g) (n : Nat) {x} (hx : f x = g x)
  proof: Nat.recOn n rfl fun n ihn => by
    simp only [iterate_succ_apply, hx, (h.iterate_left n).eq, ihn, ((refl g).iterate_right n).eq]

中文:
定理 iterate_eq_of_map_eq
  条件: (h : Commute f g) (n : 自然数) {x} (hx : f x = g x)
  证明: Nat.recOn n rfl fun n ihn => by
    simp only [iterate_succ_apply, hx, (h.iterate_left n).eq, ihn, ((refl g).iterate_right n).eq]

Depends on / 依赖: Nat.recOn, h.iterate_left, iterate_left, iterate_right, iterate_succ_apply
-/
theorem iterate_eq_of_map_eq (h : Commute f g) (n : Nat) {x} (hx : f x = g x) :
    f^[n] x = g^[n] x :=
  Nat.recOn n rfl fun n ihn => by
    simp only [iterate_succ_apply, hx, (h.iterate_left n).eq, ihn, ((refl g).iterate_right n).eq]

/--
theorem `comp_iterate` / 定理 `comp_iterate`

English:
theorem comp_iterate
  given: (h : Commute f g) (n : Nat)
  statement: (f ∘ g)^[n] = f^[n] ∘ g^[n]
  proof: by
  induction n with
  | zero => rfl
  | succ n ihn =>
    funext x
    simp only [ihn, (h.iterate_right n).eq, iterate_succ, comp_apply]

中文:
定理 comp_iterate
  条件: (h : Commute f g) (n : 自然数)
  结论: (f ∘ g)^[n] = f^[n] ∘ g^[n]
  证明: by
  induction n with
  | zero => rfl
  | succ n ihn =>
    funext x
    simp only [ihn, (h.iterate_right n).eq, iterate_succ, comp_apply]

Depends on / 依赖: comp_apply, h.iterate_right, iterate_right, iterate_succ
-/
theorem comp_iterate (h : Commute f g) (n : Nat) : (f ∘ g)^[n] = f^[n] ∘ g^[n] := by
  induction n with
  | zero => rfl
  | succ n ihn =>
    funext x
    simp only [ihn, (h.iterate_right n).eq, iterate_succ, comp_apply]

variable (f)

/--
theorem `iterate_self` / 定理 `iterate_self`

English:
theorem iterate_self
  given: (n : Nat)
  statement: Commute f^[n] f
  proof: (refl f).iterate_left n

中文:
定理 iterate_self
  条件: (n : 自然数)
  结论: Commute f^[n] f
  证明: (refl f).iterate_left n

Depends on / 依赖: iterate_left
-/
theorem iterate_self (n : Nat) : Commute f^[n] f :=
  (refl f).iterate_left n

/--
theorem `self_iterate` / 定理 `self_iterate`

English:
theorem self_iterate
  given: (n : Nat)
  statement: Commute f f^[n]
  proof: (refl f).iterate_right n

中文:
定理 self_iterate
  条件: (n : 自然数)
  结论: Commute f f^[n]
  证明: (refl f).iterate_right n

Depends on / 依赖: iterate_right
-/
theorem self_iterate (n : Nat) : Commute f f^[n] :=
  (refl f).iterate_right n

/--
theorem `iterate_iterate_self` / 定理 `iterate_iterate_self`

English:
theorem iterate_iterate_self
  given: (m n : Nat)
  statement: Commute f^[m] f^[n]
  proof: (refl f).iterate_iterate m n

中文:
定理 iterate_iterate_self
  条件: (m n : 自然数)
  结论: Commute f^[m] f^[n]
  证明: (refl f).iterate_iterate m n

Depends on / 依赖: iterate_iterate
-/
theorem iterate_iterate_self (m n : Nat) : Commute f^[m] f^[n] :=
  (refl f).iterate_iterate m n

end Commute

/--
theorem `Semiconj₂.iterate` / 定理 `Semiconj₂.iterate`

English:
theorem Semiconj₂.iterate
  given: {f : α -> α} {op : α -> α -> α} (hf : Semiconj₂ f op op) (n : Nat)
  proof: Nat.recOn n (Semiconj₂.id_left op) fun _ ihn => ihn.comp hf

中文:
定理 Semiconj₂.iterate
  条件: {f : α -> α} {op : α -> α -> α} (hf : Semiconj₂ f op op) (n : 自然数)
  证明: Nat.recOn n (Semiconj₂.id_left op) fun _ ihn => ihn.comp hf

Depends on / 依赖: Nat.recOn, id_left, ihn.comp
-/
theorem Semiconj₂.iterate {f : α -> α} {op : α -> α -> α} (hf : Semiconj₂ f op op) (n : Nat) :
    Semiconj₂ f^[n] op op :=
  Nat.recOn n (Semiconj₂.id_left op) fun _ ihn => ihn.comp hf

variable (f)

/--
theorem `iterate_succ'` / 定理 `iterate_succ'`

English:
theorem iterate_succ'
  given: (n : Nat)
  statement: f^[n.succ] = f ∘ f^[n]
  proof: by
  rw [iterate_succ]; rw [(Commute.self_iterate f n).comp_eq]

中文:
定理 iterate_succ'
  条件: (n : 自然数)
  结论: f^[n.succ] = f ∘ f^[n]
  证明: by
  rw [iterate_succ]; rw [(Commute.self_iterate f n).comp_eq]

Depends on / 依赖: Commute, Commute.self_iterate, comp_eq, iterate_succ, self_iterate
-/
theorem iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n] := by
  rw [iterate_succ]; rw [(Commute.self_iterate f n).comp_eq]

/--
theorem `iterate_succ_apply'` / 定理 `iterate_succ_apply'`

English:
theorem iterate_succ_apply'
  given: (n : Nat) (x : α)
  statement: f^[n.succ] x = f (f^[n] x)
  proof: by
  rw [iterate_succ']
  rfl

中文:
定理 iterate_succ_apply'
  条件: (n : 自然数) (x : α)
  结论: f^[n.succ] x = f (f^[n] x)
  证明: by
  rw [iterate_succ']
  rfl

Depends on / 依赖: iterate_succ
-/
theorem iterate_succ_apply' (n : Nat) (x : α) : f^[n.succ] x = f (f^[n] x) := by
  rw [iterate_succ']
  rfl

/--
theorem `iterate_pred_comp_of_pos` / 定理 `iterate_pred_comp_of_pos`

English:
theorem iterate_pred_comp_of_pos
  given: {n : Nat} (hn : 0 < n)
  statement: f^[n.pred] ∘ f = f^[n]
  proof: by
  rw [← iterate_succ]; rw [Nat.succ_pred_eq_of_pos hn]

中文:
定理 iterate_pred_comp_of_pos
  条件: {n : 自然数} (hn : 0 < n)
  结论: f^[n.pred] ∘ f = f^[n]
  证明: by
  rw [← iterate_succ]; rw [Nat.succ_pred_eq_of_pos hn]

Depends on / 依赖: Nat.succ_pred_eq_of_pos, iterate_succ, succ_pred_eq_of_pos
-/
theorem iterate_pred_comp_of_pos {n : Nat} (hn : 0 < n) : f^[n.pred] ∘ f = f^[n] := by
  rw [← iterate_succ]; rw [Nat.succ_pred_eq_of_pos hn]

/--
theorem `comp_iterate_pred_of_pos` / 定理 `comp_iterate_pred_of_pos`

English:
theorem comp_iterate_pred_of_pos
  given: {n : Nat} (hn : 0 < n)
  statement: f ∘ f^[n.pred] = f^[n]
  proof: by
  rw [← iterate_succ']; rw [Nat.succ_pred_eq_of_pos hn]

中文:
定理 comp_iterate_pred_of_pos
  条件: {n : 自然数} (hn : 0 < n)
  结论: f ∘ f^[n.pred] = f^[n]
  证明: by
  rw [← iterate_succ']; rw [Nat.succ_pred_eq_of_pos hn]

Depends on / 依赖: Nat.succ_pred_eq_of_pos, iterate_succ, succ_pred_eq_of_pos
-/
theorem comp_iterate_pred_of_pos {n : Nat} (hn : 0 < n) : f ∘ f^[n.pred] = f^[n] := by
  rw [← iterate_succ']; rw [Nat.succ_pred_eq_of_pos hn]

/-- A recursor for the iterate of a function. -/
@[elab_as_elim]
/--
Definition of `Iterate.rec` / `Iterate.rec` 的定义

English:
definition Iterate.rec
  signature: (motive : α -> Sort*) {a : α} (arg : motive a)
  body: match n with
  | 0 => arg
  | m + 1 => Iterate.rec motive (app _ arg) app m

中文:
定义 Iterate.rec
  签名: (motive : α -> 类型层*) {a : α} (arg : motive a)
  定义体: match n with
  | 0 => arg
  | m + 1 => Iterate.rec motive (app _ arg) app m

Depends on / 依赖: Iterate, Iterate.rec, motive
-/
def Iterate.rec (motive : α -> Sort*) {a : α} (arg : motive a)
    {f : α -> α} (app : forall a, motive a -> motive (f a)) (n : Nat) : motive (f^[n] a) :=
  match n with
  | 0 => arg
  | m + 1 => Iterate.rec motive (app _ arg) app m

/--
theorem `Iterate.rec_zero` / 定理 `Iterate.rec_zero`

English:
theorem Iterate.rec_zero
  statement: (motive : α -> Sort*) {f : α -> α} (app : forall a, motive a -> motive (f a))
  proof: rfl

中文:
定理 Iterate.rec_zero
  结论: (motive : α -> 类型层*) {f : α -> α} (app : 对任意 a, motive a -> motive (f a))
  证明: rfl
-/
theorem Iterate.rec_zero (motive : α -> Sort*) {f : α -> α} (app : forall a, motive a -> motive (f a))
    {a : α} (arg : motive a) : Iterate.rec motive arg app 0 = arg :=
  rfl

variable {f} {m n : Nat} {a : α}

/--
theorem `LeftInverse.iterate` / 定理 `LeftInverse.iterate`

English:
theorem LeftInverse.iterate
  given: {g : α -> α} (hg : LeftInverse g f) (n : Nat)
  proof: Nat.recOn n (fun _ => rfl) fun n ihn => by
    rw [iterate_succ']; rw [iterate_succ]
    exact ihn.comp hg

中文:
定理 左逆.iterate
  条件: {g : α -> α} (hg : 左逆 g f) (n : 自然数)
  证明: Nat.recOn n (fun _ => rfl) fun n ihn => by
    rw [iterate_succ']; rw [iterate_succ]
    exact ihn.comp hg

Depends on / 依赖: Nat.recOn, ihn.comp, iterate_succ
-/
theorem LeftInverse.iterate {g : α -> α} (hg : LeftInverse g f) (n : Nat) :
    LeftInverse g^[n] f^[n] :=
  Nat.recOn n (fun _ => rfl) fun n ihn => by
    rw [iterate_succ']; rw [iterate_succ]
    exact ihn.comp hg

/--
theorem `RightInverse.iterate` / 定理 `RightInverse.iterate`

English:
theorem RightInverse.iterate
  given: {g : α -> α} (hg : RightInverse g f) (n : Nat)
  proof: LeftInverse.iterate hg n

中文:
定理 右逆.iterate
  条件: {g : α -> α} (hg : 右逆 g f) (n : 自然数)
  证明: LeftInverse.iterate hg n

Depends on / 依赖: LeftInverse, LeftInverse.iterate, iterate
-/
theorem RightInverse.iterate {g : α -> α} (hg : RightInverse g f) (n : Nat) :
    RightInverse g^[n] f^[n] :=
  LeftInverse.iterate hg n

/--
theorem `iterate_comm` / 定理 `iterate_comm`

English:
theorem iterate_comm
  given: (f : α -> α) (m n : Nat)
  statement: f^[n]^[m] = f^[m]^[n]
  proof: (iterate_mul _ _ _).symm.trans (Eq.trans (by rw [Nat.mul_comm]) (iterate_mul _ _ _))

中文:
定理 iterate_comm
  条件: (f : α -> α) (m n : 自然数)
  结论: f^[n]^[m] = f^[m]^[n]
  证明: (iterate_mul _ _ _).symm.trans (Eq.trans (by rw [Nat.mul_comm]) (iterate_mul _ _ _))

Depends on / 依赖: Eq.trans, Nat.mul_comm, iterate_mul, mul_comm, symm.trans
-/
theorem iterate_comm (f : α -> α) (m n : Nat) : f^[n]^[m] = f^[m]^[n] :=
  (iterate_mul _ _ _).symm.trans (Eq.trans (by rw [Nat.mul_comm]) (iterate_mul _ _ _))

/--
theorem `iterate_commute` / 定理 `iterate_commute`

English:
theorem iterate_commute
  given: (m n : Nat)
  statement: Commute (fun f : α -> α => f^[m]) fun f => f^[n]
  proof: fun f => iterate_comm f m n

中文:
定理 iterate_commute
  条件: (m n : 自然数)
  结论: Commute (fun f : α -> α => f^[m]) fun f => f^[n]
  证明: fun f => iterate_comm f m n

Depends on / 依赖: iterate_comm
-/
theorem iterate_commute (m n : Nat) : Commute (fun f : α -> α => f^[m]) fun f => f^[n] :=
  fun f => iterate_comm f m n

/--
lemma `iterate_add_eq_iterate` / 引理 `iterate_add_eq_iterate`

English:
lemma iterate_add_eq_iterate
  given: (hf : Injective f)
  statement: f^[m + n] a = f^[n] a ↔ f^[m] a = a
  proof: Iff.trans (by rw [← iterate_add_apply, Nat.add_comm]) (hf.iterate n).eq_iff

alias ⟨iterate_cancel_of_add, _⟩ := iterate_add_eq_iterate

中文:
引理 iterate_add_eq_iterate
  条件: (hf : 单射 f)
  结论: f^[m + n] a = f^[n] a ↔ f^[m] a = a
  证明: Iff.trans (by rw [← iterate_add_apply, Nat.add_comm]) (hf.iterate n).eq_iff

alias ⟨iterate_cancel_of_add, _⟩ := iterate_add_eq_iterate

Depends on / 依赖: Iff.trans, Nat.add_comm, add_comm, eq_iff, hf.iterate, iterate, iterate_add_apply
-/
lemma iterate_add_eq_iterate (hf : Injective f) : f^[m + n] a = f^[n] a ↔ f^[m] a = a :=
  Iff.trans (by rw [← iterate_add_apply, Nat.add_comm]) (hf.iterate n).eq_iff

alias ⟨iterate_cancel_of_add, _⟩ := iterate_add_eq_iterate

/--
lemma `iterate_cancel` / 引理 `iterate_cancel`

English:
lemma iterate_cancel
  given: (hf : Injective f) (ha : f^[m] a = f^[n] a)
  statement: f^[m - n] a = a
  proof: by
  obtain h | h := Nat.le_total m n
  { simp [Nat.sub_eq_zero_of_le h] }
  { exact iterate_cancel_of_add hf (by rwa [Nat.sub_add_cancel h]) }

中文:
引理 iterate_cancel
  条件: (hf : 单射 f) (ha : f^[m] a = f^[n] a)
  结论: f^[m - n] a = a
  证明: by
  obtain h | h := Nat.le_total m n
  { simp [Nat.sub_eq_zero_of_le h] }
  { exact iterate_cancel_of_add hf (by rwa [Nat.sub_add_cancel h]) }

Depends on / 依赖: Nat.le_total, Nat.sub_add_cancel, Nat.sub_eq_zero_of_le, iterate_cancel_of_add, le_total, sub_add_cancel, sub_eq_zero_of_le
-/
lemma iterate_cancel (hf : Injective f) (ha : f^[m] a = f^[n] a) : f^[m - n] a = a := by
  obtain h | h := Nat.le_total m n
  { simp [Nat.sub_eq_zero_of_le h] }
  { exact iterate_cancel_of_add hf (by rwa [Nat.sub_add_cancel h]) }

/--
theorem `involutive_iff_iter_2_eq_id` / 定理 `involutive_iff_iter_2_eq_id`

English:
theorem involutive_iff_iter_2_eq_id
  given: {α} {f : α -> α}
  statement: Involutive f ↔ f^[2] = id
  proof: funext_iff.symm

中文:
定理 involutive_iff_iter_2_eq_id
  条件: {α} {f : α -> α}
  结论: 对合 f ↔ f^[2] = id
  证明: funext_iff.symm

Depends on / 依赖: funext_iff, funext_iff.symm
-/
theorem involutive_iff_iter_2_eq_id {α} {f : α -> α} : Involutive f ↔ f^[2] = id :=
  funext_iff.symm

end Function

namespace List

open Function

/--
theorem `foldl_const` / 定理 `foldl_const`

English:
theorem foldl_const
  given: (f : α -> α) (a : α) (l : List β)
  proof: by
  induction l generalizing a with
  | nil => rfl
  | cons b l H => rw [length_cons, foldl, iterate_succ_apply, H]

中文:
定理 foldl_const
  条件: (f : α -> α) (a : α) (l : 列表 β)
  证明: by
  induction l generalizing a with
  | nil => rfl
  | cons b l H => rw [length_cons, foldl, iterate_succ_apply, H]

Depends on / 依赖: generalizing, iterate_succ_apply, length_cons
-/
theorem foldl_const (f : α -> α) (a : α) (l : List β) :
    l.foldl (fun b _ => f b) a = f^[l.length] a := by
  induction l generalizing a with
  | nil => rfl
  | cons b l H => rw [length_cons, foldl, iterate_succ_apply, H]

/--
theorem `foldr_const` / 定理 `foldr_const`

English:
theorem foldr_const
  given: (f : β -> β) (b : β)
  statement: forall l : List α, l.foldr (fun _ => f) b = f^[l.length] b

中文:
定理 foldr_const
  条件: (f : β -> β) (b : β)
  结论: 对任意 l : 列表 α, l.foldr (fun _ => f) b = f^[l.length] b
-/
theorem foldr_const (f : β -> β) (b : β) : forall l : List α, l.foldr (fun _ => f) b = f^[l.length] b
  | [] => rfl
  | a :: l => by rw [length_cons, foldr, foldr_const f b l, iterate_succ_apply']

end List

namespace Pi

variable {ι : Type*}

@[simp]
/--
theorem `map_iterate` / 定理 `map_iterate`

English:
theorem map_iterate
  given: {α : ι -> Type*} (f : forall i, α i -> α i) (n : Nat)
  proof: by
  induction n <;> simp [*, map_comp_map]

中文:
定理 map_iterate
  条件: {α : ι -> 类型} (f : 对任意 i, α i -> α i) (n : 自然数)
  证明: by
  induction n <;> simp [*, map_comp_map]

Depends on / 依赖: map_comp_map
-/
theorem map_iterate {α : ι -> Type*} (f : forall i, α i -> α i) (n : Nat) :
    (Pi.map f)^[n] = Pi.map fun i => (f i)^[n] := by
  induction n <;> simp [*, map_comp_map]

end Pi
