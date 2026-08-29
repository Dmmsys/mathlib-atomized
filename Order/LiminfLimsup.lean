/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Rémy Degenne
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Order.Filter.IsBounded
public import Mathlib.Order.Hom.CompleteLattice

/-!
# liminfs and limsups of functions and filters

Defines the liminf/limsup of a function taking values in a conditionally complete lattice, with
respect to an arbitrary filter.

We define `limsSup f` (`limsInf f`) where `f` is a filter taking values in a conditionally complete
lattice. `limsSup f` is the smallest element `a` such that, eventually, `u ≤ a` (and vice versa for
`limsInf f`). To work with the Limsup along a function `u` use `limsSup (map u f)`.

Usually, one defines the Limsup as `inf (sup s)` where the Inf is taken over all sets in the filter.
For instance, in ℕ along a function `u`, this is `inf_n (sup_{k ≥ n} u k)` (and the latter quantity
decreases with `n`, so this is in fact a limit.). There is however a difficulty: it is well possible
that `u` is not bounded on the whole space, only eventually (think of `limsup (fun x ↦ 1/x)` on ℝ).
Then there is no guarantee that the quantity above really decreases (the value of the `sup`
beforehand is not really well defined, as one cannot use ∞), so that the Inf could be anything.
So one cannot use this `inf sup ...` definition in conditionally complete lattices, and one has
to use a less tractable definition.

In conditionally complete lattices, the definition is only useful for filters which are eventually
bounded above (otherwise, the Limsup would morally be +∞, which does not belong to the space) and
which are frequently bounded below (otherwise, the Limsup would morally be -∞, which is not in the
space either). We start with definitions of these concepts for arbitrary filters, before turning to
the definitions of Limsup and Liminf.

In complete lattices, however, it coincides with the `Inf Sup` definition.
-/

@[expose] public section

open Filter Set Function

variable {α β γ ι ι' : Type*}

namespace Filter

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s : Set α} {u : β -> α}

/--
Definition of `limsSup` / `limsSup` 的定义

English:
definition limsSup
  signature: (f : Filter α)
  body: sInf { a | forallᶠ n in f, n <= a }

中文:
定义 limsSup
  签名: (f : 滤子 α)
  定义体: sInf { a | forallᶠ n in f, n <= a }
-/
def limsSup (f : Filter α) : α :=
  sInf { a | forallᶠ n in f, n <= a }

/--
Definition of `limsInf` / `limsInf` 的定义

English:
definition limsInf
  signature: (f : Filter α)
  body: sSup { a | forallᶠ n in f, a <= n }

中文:
定义 limsInf
  签名: (f : 滤子 α)
  定义体: sSup { a | forallᶠ n in f, a <= n }
-/
def limsInf (f : Filter α) : α :=
  sSup { a | forallᶠ n in f, a <= n }

/--
Definition of `limsup` / `limsup` 的定义

English:
definition limsup
  signature: (u : β -> α) (f : Filter β)
  body: limsSup (map u f)

中文:
定义 limsup
  签名: (u : β -> α) (f : 滤子 β)
  定义体: limsSup (map u f)

Depends on / 依赖: limsSup
-/
def limsup (u : β -> α) (f : Filter β) : α :=
  limsSup (map u f)

/--
Definition of `liminf` / `liminf` 的定义

English:
definition liminf
  signature: (u : β -> α) (f : Filter β)
  body: limsInf (map u f)

中文:
定义 liminf
  签名: (u : β -> α) (f : 滤子 β)
  定义体: limsInf (map u f)

Depends on / 依赖: limsInf
-/
def liminf (u : β -> α) (f : Filter β) : α :=
  limsInf (map u f)

/--
Definition of `blimsup` / `blimsup` 的定义

English:
definition blimsup
  signature: (u : β -> α) (f : Filter β) (p : β -> Prop)
  body: sInf { a | forallᶠ x in f, p x -> u x <= a }

中文:
定义 blimsup
  签名: (u : β -> α) (f : 滤子 β) (p : β -> 命题)
  定义体: sInf { a | forallᶠ x in f, p x -> u x <= a }
-/
def blimsup (u : β -> α) (f : Filter β) (p : β -> Prop) :=
  sInf { a | forallᶠ x in f, p x -> u x <= a }

/--
Definition of `bliminf` / `bliminf` 的定义

English:
definition bliminf
  signature: (u : β -> α) (f : Filter β) (p : β -> Prop)
  body: sSup { a | forallᶠ x in f, p x -> a <= u x }

中文:
定义 bliminf
  签名: (u : β -> α) (f : 滤子 β) (p : β -> 命题)
  定义体: sSup { a | forallᶠ x in f, p x -> a <= u x }
-/
def bliminf (u : β -> α) (f : Filter β) (p : β -> Prop) :=
  sSup { a | forallᶠ x in f, p x -> a <= u x }

section

variable {f : Filter β} {u : β -> α} {p : β -> Prop}

/--
theorem `limsup_eq` / 定理 `limsup_eq`

English:
theorem limsup_eq
  statement: limsup u f = sInf { a | forallᶠ n in f, u n <= a }
  proof: rfl

中文:
定理 limsup_eq
  结论: limsup u f = sInf { a | 对任意ᶠ n in f, u n <= a }
  证明: rfl
-/
theorem limsup_eq : limsup u f = sInf { a | forallᶠ n in f, u n <= a } :=
  rfl

/--
theorem `liminf_eq` / 定理 `liminf_eq`

English:
theorem liminf_eq
  statement: liminf u f = sSup { a | forallᶠ n in f, a <= u n }
  proof: rfl

中文:
定理 liminf_eq
  结论: liminf u f = sSup { a | 对任意ᶠ n in f, a <= u n }
  证明: rfl
-/
theorem liminf_eq : liminf u f = sSup { a | forallᶠ n in f, a <= u n } :=
  rfl

/--
theorem `blimsup_eq` / 定理 `blimsup_eq`

English:
theorem blimsup_eq
  statement: blimsup u f p = sInf { a | forallᶠ x in f, p x -> u x <= a }
  proof: rfl

中文:
定理 blimsup_eq
  结论: blimsup u f p = sInf { a | 对任意ᶠ x in f, p x -> u x <= a }
  证明: rfl
-/
theorem blimsup_eq : blimsup u f p = sInf { a | forallᶠ x in f, p x -> u x <= a } :=
  rfl

/--
theorem `bliminf_eq` / 定理 `bliminf_eq`

English:
theorem bliminf_eq
  statement: bliminf u f p = sSup { a | forallᶠ x in f, p x -> a <= u x }
  proof: rfl

中文:
定理 bliminf_eq
  结论: bliminf u f p = sSup { a | 对任意ᶠ x in f, p x -> a <= u x }
  证明: rfl
-/
theorem bliminf_eq : bliminf u f p = sSup { a | forallᶠ x in f, p x -> a <= u x } :=
  rfl

/--
lemma `liminf_comp` / 引理 `liminf_comp`

English:
lemma liminf_comp
  given: (u : β -> α) (v : γ -> β) (f : Filter γ)
  proof: rfl

中文:
引理 liminf_comp
  条件: (u : β -> α) (v : γ -> β) (f : 滤子 γ)
  证明: rfl
-/
lemma liminf_comp (u : β -> α) (v : γ -> β) (f : Filter γ) :
    liminf (u ∘ v) f = liminf u (map v f) := rfl

/--
lemma `limsup_comp` / 引理 `limsup_comp`

English:
lemma limsup_comp
  given: (u : β -> α) (v : γ -> β) (f : Filter γ)
  proof: rfl

中文:
引理 limsup_comp
  条件: (u : β -> α) (v : γ -> β) (f : 滤子 γ)
  证明: rfl
-/
lemma limsup_comp (u : β -> α) (v : γ -> β) (f : Filter γ) :
    limsup (u ∘ v) f = limsup u (map v f) := rfl

end

@[simp]
/--
theorem `blimsup_true` / 定理 `blimsup_true`

English:
theorem blimsup_true
  given: (f : Filter β) (u : β -> α)
  statement: (blimsup u f fun _ => True) = limsup u f
  proof: by
  simp [blimsup_eq, limsup_eq]

@[simp]

中文:
定理 blimsup_true
  条件: (f : 滤子 β) (u : β -> α)
  结论: (blimsup u f fun _ => 真) = limsup u f
  证明: by
  simp [blimsup_eq, limsup_eq]

@[simp]

Depends on / 依赖: blimsup_eq, limsup_eq
-/
theorem blimsup_true (f : Filter β) (u : β -> α) : (blimsup u f fun _ => True) = limsup u f := by
  simp [blimsup_eq, limsup_eq]

@[simp]
/--
theorem `bliminf_true` / 定理 `bliminf_true`

English:
theorem bliminf_true
  given: (f : Filter β) (u : β -> α)
  statement: (bliminf u f fun _ => True) = liminf u f
  proof: by
  simp [bliminf_eq, liminf_eq]

中文:
定理 bliminf_true
  条件: (f : 滤子 β) (u : β -> α)
  结论: (bliminf u f fun _ => 真) = liminf u f
  证明: by
  simp [bliminf_eq, liminf_eq]

Depends on / 依赖: bliminf_eq, liminf_eq
-/
theorem bliminf_true (f : Filter β) (u : β -> α) : (bliminf u f fun _ => True) = liminf u f := by
  simp [bliminf_eq, liminf_eq]

/--
lemma `blimsup_eq_limsup` / 引理 `blimsup_eq_limsup`

English:
lemma blimsup_eq_limsup
  given: {f : Filter β} {u : β -> α} {p : β -> Prop}
  proof: by
  simp only [blimsup_eq, limsup_eq, eventually_inf_principal, mem_ofPred_eq]

中文:
引理 blimsup_eq_limsup
  条件: {f : 滤子 β} {u : β -> α} {p : β -> 命题}
  证明: by
  simp only [blimsup_eq, limsup_eq, eventually_inf_principal, mem_ofPred_eq]

Depends on / 依赖: blimsup_eq, eventually_inf_principal, limsup_eq, mem_ofPred_eq
-/
lemma blimsup_eq_limsup {f : Filter β} {u : β -> α} {p : β -> Prop} :
    blimsup u f p = limsup u (f ⊓ 𝓟 {x | p x}) := by
  simp only [blimsup_eq, limsup_eq, eventually_inf_principal, mem_ofPred_eq]

/--
lemma `bliminf_eq_liminf` / 引理 `bliminf_eq_liminf`

English:
lemma bliminf_eq_liminf
  given: {f : Filter β} {u : β -> α} {p : β -> Prop}
  proof: blimsup_eq_limsup (α := αᵒᵈ)

中文:
引理 bliminf_eq_liminf
  条件: {f : 滤子 β} {u : β -> α} {p : β -> 命题}
  证明: blimsup_eq_limsup (α := αᵒᵈ)

Depends on / 依赖: blimsup_eq_limsup
-/
lemma bliminf_eq_liminf {f : Filter β} {u : β -> α} {p : β -> Prop} :
    bliminf u f p = liminf u (f ⊓ 𝓟 {x | p x}) :=
  blimsup_eq_limsup (α := αᵒᵈ)

/--
theorem `blimsup_eq_limsup_subtype` / 定理 `blimsup_eq_limsup_subtype`

English:
theorem blimsup_eq_limsup_subtype
  given: {f : Filter β} {u : β -> α} {p : β -> Prop}
  proof: by
  rw [blimsup_eq_limsup]; rw [limsup]; rw [limsup]; rw [← map_map]; rw [map_comap_setCoe_val]

中文:
定理 blimsup_eq_limsup_subtype
  条件: {f : 滤子 β} {u : β -> α} {p : β -> 命题}
  证明: by
  rw [blimsup_eq_limsup]; rw [limsup]; rw [limsup]; rw [← map_map]; rw [map_comap_setCoe_val]

Depends on / 依赖: blimsup_eq_limsup, limsup, map_comap_setCoe_val, map_map
-/
theorem blimsup_eq_limsup_subtype {f : Filter β} {u : β -> α} {p : β -> Prop} :
    blimsup u f p = limsup (u ∘ ((↑) : { x | p x } -> β)) (comap (↑) f) := by
  rw [blimsup_eq_limsup]; rw [limsup]; rw [limsup]; rw [← map_map]; rw [map_comap_setCoe_val]

/--
theorem `bliminf_eq_liminf_subtype` / 定理 `bliminf_eq_liminf_subtype`

English:
theorem bliminf_eq_liminf_subtype
  given: {f : Filter β} {u : β -> α} {p : β -> Prop}
  proof: blimsup_eq_limsup_subtype (α := αᵒᵈ)

中文:
定理 bliminf_eq_liminf_subtype
  条件: {f : 滤子 β} {u : β -> α} {p : β -> 命题}
  证明: blimsup_eq_limsup_subtype (α := αᵒᵈ)

Depends on / 依赖: blimsup_eq_limsup_subtype
-/
theorem bliminf_eq_liminf_subtype {f : Filter β} {u : β -> α} {p : β -> Prop} :
    bliminf u f p = liminf (u ∘ ((↑) : { x | p x } -> β)) (comap (↑) f) :=
  blimsup_eq_limsup_subtype (α := αᵒᵈ)

/--
theorem `limsSup_le_of_le` / 定理 `limsSup_le_of_le`

English:
theorem limsSup_le_of_le
  statement: {f : Filter α} {a}
  proof: csInf_le hf h

中文:
定理 limsSup_le_of_le
  结论: {f : 滤子 α} {a}
  证明: csInf_le hf h

Depends on / 依赖: csInf_le, isBoundedDefault, limsSup
-/
theorem limsSup_le_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· <= ·) := by isBoundedDefault)
    (h : forallᶠ n in f, n <= a) : limsSup f <= a :=
  csInf_le hf h

/--
theorem `le_limsInf_of_le` / 定理 `le_limsInf_of_le`

English:
theorem le_limsInf_of_le
  statement: {f : Filter α} {a}
  proof: le_csSup hf h

中文:
定理 le_limsInf_of_le
  结论: {f : 滤子 α} {a}
  证明: le_csSup hf h

Depends on / 依赖: isBoundedDefault, le_csSup, limsInf
-/
theorem le_limsInf_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· >= ·) := by isBoundedDefault)
    (h : forallᶠ n in f, a <= n) : a <= limsInf f :=
  le_csSup hf h

/--
theorem `limsup_le_of_le` / 定理 `limsup_le_of_le`

English:
theorem limsup_le_of_le
  statement: {f : Filter β} {u : β -> α} {a}
  proof: csInf_le hf h

中文:
定理 limsup_le_of_le
  结论: {f : 滤子 β} {u : β -> α} {a}
  证明: csInf_le hf h

Depends on / 依赖: csInf_le, isBoundedDefault, limsup
-/
theorem limsup_le_of_le {f : Filter β} {u : β -> α} {a}
    (hf : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
    (h : forallᶠ n in f, u n <= a) : limsup u f <= a :=
  csInf_le hf h

/--
theorem `le_liminf_of_le` / 定理 `le_liminf_of_le`

English:
theorem le_liminf_of_le
  statement: {f : Filter β} {u : β -> α} {a}
  proof: le_csSup hf h

中文:
定理 le_liminf_of_le
  结论: {f : 滤子 β} {u : β -> α} {a}
  证明: le_csSup hf h

Depends on / 依赖: isBoundedDefault, le_csSup, liminf
-/
theorem le_liminf_of_le {f : Filter β} {u : β -> α} {a}
    (hf : f.IsCoboundedUnder (· >= ·) u := by isBoundedDefault)
    (h : forallᶠ n in f, a <= u n) : a <= liminf u f :=
  le_csSup hf h

/--
theorem `le_limsSup_of_le` / 定理 `le_limsSup_of_le`

English:
theorem le_limsSup_of_le
  statement: {f : Filter α} {a}
  proof: le_csInf hf h

中文:
定理 le_limsSup_of_le
  结论: {f : 滤子 α} {a}
  证明: le_csInf hf h

Depends on / 依赖: isBoundedDefault, le_csInf, limsSup
-/
theorem le_limsSup_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· <= ·) := by isBoundedDefault)
    (h : forall b, (forallᶠ n in f, n <= b) -> a <= b) : a <= limsSup f :=
  le_csInf hf h

/--
theorem `limsInf_le_of_le` / 定理 `limsInf_le_of_le`

English:
theorem limsInf_le_of_le
  statement: {f : Filter α} {a}
  proof: csSup_le hf h

中文:
定理 limsInf_le_of_le
  结论: {f : 滤子 α} {a}
  证明: csSup_le hf h

Depends on / 依赖: csSup_le, isBoundedDefault, limsInf
-/
theorem limsInf_le_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· >= ·) := by isBoundedDefault)
    (h : forall b, (forallᶠ n in f, b <= n) -> b <= a) : limsInf f <= a :=
  csSup_le hf h

/--
theorem `le_limsup_of_le` / 定理 `le_limsup_of_le`

English:
theorem le_limsup_of_le
  statement: {f : Filter β} {u : β -> α} {a}
  proof: le_csInf hf h

中文:
定理 le_limsup_of_le
  结论: {f : 滤子 β} {u : β -> α} {a}
  证明: le_csInf hf h

Depends on / 依赖: isBoundedDefault, le_csInf, limsup
-/
theorem le_limsup_of_le {f : Filter β} {u : β -> α} {a}
    (hf : f.IsBoundedUnder (· <= ·) u := by isBoundedDefault)
    (h : forall b, (forallᶠ n in f, u n <= b) -> a <= b) : a <= limsup u f :=
  le_csInf hf h

/--
theorem `liminf_le_of_le` / 定理 `liminf_le_of_le`

English:
theorem liminf_le_of_le
  statement: {f : Filter β} {u : β -> α} {a}
  proof: csSup_le hf h

中文:
定理 liminf_le_of_le
  结论: {f : 滤子 β} {u : β -> α} {a}
  证明: csSup_le hf h

Depends on / 依赖: csSup_le, isBoundedDefault, liminf
-/
theorem liminf_le_of_le {f : Filter β} {u : β -> α} {a}
    (hf : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault)
    (h : forall b, (forallᶠ n in f, b <= u n) -> b <= a) : liminf u f <= a :=
  csSup_le hf h

/--
theorem `limsInf_le_limsSup` / 定理 `limsInf_le_limsSup`

English:
theorem limsInf_le_limsSup
  statement: {f : Filter α} [NeBot f]
  proof: liminf_le_of_le h₂ fun a₀ ha₀ =>
    le_limsup_of_le h₁ fun a₁ ha₁ =>
      show a₀ <= a₁ from
        let ⟨_, hb₀, hb₁⟩ := (ha₀.and ha₁).exists
        le_trans hb₀ hb₁

中文:
定理 limsInf_le_limsSup
  结论: {f : 滤子 α} [NeBot f]
  证明: liminf_le_of_le h₂ fun a₀ ha₀ =>
    le_limsup_of_le h₁ fun a₁ ha₁ =>
      show a₀ <= a₁ from
        let ⟨_, hb₀, hb₁⟩ := (ha₀.and ha₁).exists
        le_trans hb₀ hb₁

Depends on / 依赖: IsBounded, f.IsBounded, isBoundedDefault, le_limsup_of_le, le_trans, liminf_le_of_le, limsInf, limsSup
-/
theorem limsInf_le_limsSup {f : Filter α} [NeBot f]
    (h₁ : f.IsBounded (· <= ·) := by isBoundedDefault)
    (h₂ : f.IsBounded (· >= ·) := by isBoundedDefault) :
    limsInf f <= limsSup f :=
  liminf_le_of_le h₂ fun a₀ ha₀ =>
    le_limsup_of_le h₁ fun a₁ ha₁ =>
      show a₀ <= a₁ from
        let ⟨_, hb₀, hb₁⟩ := (ha₀.and ha₁).exists
        le_trans hb₀ hb₁

/--
theorem `liminf_le_limsup` / 定理 `liminf_le_limsup`

English:
theorem liminf_le_limsup
  statement: {f : Filter β} [NeBot f] {u : β -> α}
  proof: limsInf_le_limsSup h h'

中文:
定理 liminf_le_limsup
  结论: {f : 滤子 β} [NeBot f] {u : β -> α}
  证明: limsInf_le_limsSup h h'

Depends on / 依赖: IsBoundedUnder, f.IsBoundedUnder, isBoundedDefault, liminf, limsInf_le_limsSup, limsup
-/
theorem liminf_le_limsup {f : Filter β} [NeBot f] {u : β -> α}
    (h : f.IsBoundedUnder (· <= ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault) :
    liminf u f <= limsup u f :=
  limsInf_le_limsSup h h'

/--
theorem `limsSup_le_limsSup` / 定理 `limsSup_le_limsSup`

English:
theorem limsSup_le_limsSup
  statement: {f g : Filter α}
  proof: csInf_le_csInf hf hg h

中文:
定理 limsSup_le_limsSup
  结论: {f g : 滤子 α}
  证明: csInf_le_csInf hf hg h

Depends on / 依赖: IsBounded, csInf_le_csInf, g.IsBounded, isBoundedDefault, limsSup
-/
theorem limsSup_le_limsSup {f g : Filter α}
    (hf : f.IsCobounded (· <= ·) := by isBoundedDefault)
    (hg : g.IsBounded (· <= ·) := by isBoundedDefault)
    (h : forall a, (forallᶠ n in g, n <= a) -> forallᶠ n in f, n <= a) : limsSup f <= limsSup g :=
  csInf_le_csInf hf hg h

/--
theorem `limsInf_le_limsInf` / 定理 `limsInf_le_limsInf`

English:
theorem limsInf_le_limsInf
  statement: {f g : Filter α}
  proof: csSup_le_csSup hg hf h

中文:
定理 limsInf_le_limsInf
  结论: {f g : 滤子 α}
  证明: csSup_le_csSup hg hf h

Depends on / 依赖: IsCobounded, csSup_le_csSup, g.IsCobounded, isBoundedDefault, limsInf
-/
theorem limsInf_le_limsInf {f g : Filter α}
    (hf : f.IsBounded (· >= ·) := by isBoundedDefault)
    (hg : g.IsCobounded (· >= ·) := by isBoundedDefault)
    (h : forall a, (forallᶠ n in f, a <= n) -> forallᶠ n in g, a <= n) : limsInf f <= limsInf g :=
  csSup_le_csSup hg hf h

/--
theorem `limsup_le_limsup` / 定理 `limsup_le_limsup`

English:
theorem limsup_le_limsup
  statement: {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α -> β}
  proof: limsSup_le_limsSup hu hv fun _ => h.trans

中文:
定理 limsup_le_limsup
  结论: {α : 类型} [条件完备格 β] {f : 滤子 α} {u v : α -> β}
  证明: limsSup_le_limsSup hu hv fun _ => h.trans

Depends on / 依赖: IsBoundedUnder, f.IsBoundedUnder, h.trans, isBoundedDefault, limsSup_le_limsSup, limsup
-/
theorem limsup_le_limsup {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α -> β}
    (h : u <=ᶠ[f] v)
    (hu : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
    (hv : f.IsBoundedUnder (· <= ·) v := by isBoundedDefault) :
    limsup u f <= limsup v f :=
  limsSup_le_limsSup hu hv fun _ => h.trans

/--
theorem `liminf_le_liminf` / 定理 `liminf_le_liminf`

English:
theorem liminf_le_liminf
  statement: {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α -> β}
  proof: limsup_le_limsup (β := βᵒᵈ) h hv hu

中文:
定理 liminf_le_liminf
  结论: {α : 类型} [条件完备格 β] {f : 滤子 α} {u v : α -> β}
  证明: limsup_le_limsup (β := βᵒᵈ) h hv hu

Depends on / 依赖: IsCoboundedUnder, f.IsCoboundedUnder, isBoundedDefault, liminf, limsup_le_limsup
-/
theorem liminf_le_liminf {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α -> β}
    (h : forallᶠ a in f, u a <= v a)
    (hu : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault)
    (hv : f.IsCoboundedUnder (· >= ·) v := by isBoundedDefault) :
    liminf u f <= liminf v f :=
  limsup_le_limsup (β := βᵒᵈ) h hv hu

/--
theorem `limsSup_le_limsSup_of_le` / 定理 `limsSup_le_limsSup_of_le`

English:
theorem limsSup_le_limsSup_of_le
  statement: {f g : Filter α} (h : f <= g)
  proof: limsSup_le_limsSup hf hg fun _ ha => h ha

中文:
定理 limsSup_le_limsSup_of_le
  结论: {f g : 滤子 α} (h : f <= g)
  证明: limsSup_le_limsSup hf hg fun _ ha => h ha

Depends on / 依赖: IsBounded, g.IsBounded, isBoundedDefault, limsSup, limsSup_le_limsSup
-/
theorem limsSup_le_limsSup_of_le {f g : Filter α} (h : f <= g)
    (hf : f.IsCobounded (· <= ·) := by isBoundedDefault)
    (hg : g.IsBounded (· <= ·) := by isBoundedDefault) :
    limsSup f <= limsSup g :=
  limsSup_le_limsSup hf hg fun _ ha => h ha

/--
theorem `limsInf_le_limsInf_of_le` / 定理 `limsInf_le_limsInf_of_le`

English:
theorem limsInf_le_limsInf_of_le
  statement: {f g : Filter α} (h : g <= f)
  proof: limsInf_le_limsInf hf hg fun _ ha => h ha

中文:
定理 limsInf_le_limsInf_of_le
  结论: {f g : 滤子 α} (h : g <= f)
  证明: limsInf_le_limsInf hf hg fun _ ha => h ha

Depends on / 依赖: IsCobounded, g.IsCobounded, isBoundedDefault, limsInf, limsInf_le_limsInf
-/
theorem limsInf_le_limsInf_of_le {f g : Filter α} (h : g <= f)
    (hf : f.IsBounded (· >= ·) := by isBoundedDefault)
    (hg : g.IsCobounded (· >= ·) := by isBoundedDefault) :
    limsInf f <= limsInf g :=
  limsInf_le_limsInf hf hg fun _ ha => h ha

/--
theorem `limsup_le_limsup_of_le` / 定理 `limsup_le_limsup_of_le`

English:
theorem limsup_le_limsup_of_le
  statement: {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : f <= g)
  proof: limsSup_le_limsSup_of_le (map_mono h) hf hg

中文:
定理 limsup_le_limsup_of_le
  结论: {α β} [条件完备格 β] {f g : 滤子 α} (h : f <= g)
  证明: limsSup_le_limsSup_of_le (map_mono h) hf hg

Depends on / 依赖: IsBoundedUnder, g.IsBoundedUnder, isBoundedDefault, limsSup_le_limsSup_of_le, limsup, map_mono
-/
theorem limsup_le_limsup_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : f <= g)
    {u : α -> β}
    (hf : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
    (hg : g.IsBoundedUnder (· <= ·) u := by isBoundedDefault) :
    limsup u f <= limsup u g :=
  limsSup_le_limsSup_of_le (map_mono h) hf hg

/--
theorem `Tendsto.limsup_comp_le_limsup` / 定理 `Tendsto.limsup_comp_le_limsup`

English:
theorem Tendsto.limsup_comp_le_limsup
  statement: {ι α β} [ConditionallyCompleteLattice β] {v : ι -> α}
  proof: by
  rw [limsup_comp]
  exact limsup_le_limsup_of_le hv

中文:
定理 收敛.limsup_comp_le_limsup
  结论: {ι α β} [条件完备格 β] {v : ι -> α}
  证明: by
  rw [limsup_comp]
  exact limsup_le_limsup_of_le hv

Depends on / 依赖: IsBoundedUnder, g.IsBoundedUnder, isBoundedDefault, limsup, limsup_comp, limsup_le_limsup_of_le
-/
theorem Tendsto.limsup_comp_le_limsup {ι α β} [ConditionallyCompleteLattice β] {v : ι -> α}
    {u : α -> β} {f : Filter ι} {g : Filter α} (hv : Tendsto v f g)
    (hvf : (map v f).IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
    (hg : g.IsBoundedUnder (· <= ·) u := by isBoundedDefault) :
    limsup (u ∘ v) f <= limsup u g := by
  rw [limsup_comp]
  exact limsup_le_limsup_of_le hv

/--
theorem `liminf_le_liminf_of_le` / 定理 `liminf_le_liminf_of_le`

English:
theorem liminf_le_liminf_of_le
  statement: {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : g <= f)
  proof: limsInf_le_limsInf_of_le (map_mono h) hf hg

中文:
定理 liminf_le_liminf_of_le
  结论: {α β} [条件完备格 β] {f g : 滤子 α} (h : g <= f)
  证明: limsInf_le_limsInf_of_le (map_mono h) hf hg

Depends on / 依赖: IsCoboundedUnder, g.IsCoboundedUnder, isBoundedDefault, liminf, limsInf_le_limsInf_of_le, map_mono
-/
theorem liminf_le_liminf_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : g <= f)
    {u : α -> β}
    (hf : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault)
    (hg : g.IsCoboundedUnder (· >= ·) u := by isBoundedDefault) :
    liminf u f <= liminf u g :=
  limsInf_le_limsInf_of_le (map_mono h) hf hg

/--
theorem `Tendsto.liminf_le_liminf_comp` / 定理 `Tendsto.liminf_le_liminf_comp`

English:
theorem Tendsto.liminf_le_liminf_comp
  statement: {ι α β} [ConditionallyCompleteLattice β] {v : ι -> α}
  proof: hv.limsup_comp_le_limsup (β := βᵒᵈ)

中文:
定理 收敛.liminf_le_liminf_comp
  结论: {ι α β} [条件完备格 β] {v : ι -> α}
  证明: hv.limsup_comp_le_limsup (β := βᵒᵈ)

Depends on / 依赖: IsBoundedUnder, g.IsBoundedUnder, hv.limsup_comp_le_limsup, isBoundedDefault, liminf, limsup_comp_le_limsup
-/
theorem Tendsto.liminf_le_liminf_comp {ι α β} [ConditionallyCompleteLattice β] {v : ι -> α}
    {u : α -> β} {f : Filter ι} {g : Filter α} (hv : Tendsto v f g)
    (hvf : (map v f).IsCoboundedUnder (· >= ·) u := by isBoundedDefault)
    (hg : g.IsBoundedUnder (· >= ·) u := by isBoundedDefault) :
    liminf u g <= liminf (u ∘ v) f :=
  hv.limsup_comp_le_limsup (β := βᵒᵈ)

/--
lemma `limsSup_principal_eq_csSup` / 引理 `limsSup_principal_eq_csSup`

English:
lemma limsSup_principal_eq_csSup
  given: (h : BddAbove s) (hs : s.Nonempty)
  statement: limsSup (𝓟 s) = sSup s
  proof: by
  simp only [limsSup, eventually_principal]; exact csInf_upperBounds_eq_csSup h hs

中文:
引理 limsSup_principal_eq_csSup
  条件: (h : BddAbove s) (hs : s.非空)
  结论: limsSup (𝓟 s) = sSup s
  证明: by
  simp only [limsSup, eventually_principal]; exact csInf_upperBounds_eq_csSup h hs

Depends on / 依赖: csInf_upperBounds_eq_csSup, eventually_principal, limsSup
-/
lemma limsSup_principal_eq_csSup (h : BddAbove s) (hs : s.Nonempty) : limsSup (𝓟 s) = sSup s := by
  simp only [limsSup, eventually_principal]; exact csInf_upperBounds_eq_csSup h hs

/--
lemma `limsInf_principal_eq_csSup` / 引理 `limsInf_principal_eq_csSup`

English:
lemma limsInf_principal_eq_csSup
  given: (h : BddBelow s) (hs : s.Nonempty)
  statement: limsInf (𝓟 s) = sInf s
  proof: limsSup_principal_eq_csSup (α := αᵒᵈ) h hs

中文:
引理 limsInf_principal_eq_csSup
  条件: (h : BddBelow s) (hs : s.非空)
  结论: limsInf (𝓟 s) = sInf s
  证明: limsSup_principal_eq_csSup (α := αᵒᵈ) h hs

Depends on / 依赖: limsSup_principal_eq_csSup
-/
lemma limsInf_principal_eq_csSup (h : BddBelow s) (hs : s.Nonempty) : limsInf (𝓟 s) = sInf s :=
  limsSup_principal_eq_csSup (α := αᵒᵈ) h hs

/--
lemma `limsup_top_eq_ciSup` / 引理 `limsup_top_eq_ciSup`

English:
lemma limsup_top_eq_ciSup
  given: [Nonempty β] (hu : BddAbove (range u))
  statement: limsup u ⊤ = ⨆ i, u i
  proof: by
  rw [limsup]; rw [map_top]; rw [limsSup_principal_eq_csSup hu (range_nonempty _)]; rw [sSup_range]

中文:
引理 limsup_top_eq_ciSup
  条件: [非空 β] (hu : BddAbove (range u))
  结论: limsup u ⊤ = ⨆ i, u i
  证明: by
  rw [limsup]; rw [map_top]; rw [limsSup_principal_eq_csSup hu (range_nonempty _)]; rw [sSup_range]

Depends on / 依赖: limsSup_principal_eq_csSup, limsup, map_top, range_nonempty, sSup_range
-/
lemma limsup_top_eq_ciSup [Nonempty β] (hu : BddAbove (range u)) : limsup u ⊤ = ⨆ i, u i := by
  rw [limsup]; rw [map_top]; rw [limsSup_principal_eq_csSup hu (range_nonempty _)]; rw [sSup_range]

/--
lemma `liminf_top_eq_ciInf` / 引理 `liminf_top_eq_ciInf`

English:
lemma liminf_top_eq_ciInf
  given: [Nonempty β] (hu : BddBelow (range u))
  statement: liminf u ⊤ = ⨅ i, u i
  proof: by
  rw [liminf]; rw [map_top]; rw [limsInf_principal_eq_csSup hu (range_nonempty _)]; rw [sInf_range]

中文:
引理 liminf_top_eq_ciInf
  条件: [非空 β] (hu : BddBelow (range u))
  结论: liminf u ⊤ = ⨅ i, u i
  证明: by
  rw [liminf]; rw [map_top]; rw [limsInf_principal_eq_csSup hu (range_nonempty _)]; rw [sInf_range]

Depends on / 依赖: liminf, limsInf_principal_eq_csSup, map_top, range_nonempty, sInf_range
-/
lemma liminf_top_eq_ciInf [Nonempty β] (hu : BddBelow (range u)) : liminf u ⊤ = ⨅ i, u i := by
  rw [liminf]; rw [map_top]; rw [limsInf_principal_eq_csSup hu (range_nonempty _)]; rw [sInf_range]

/--
theorem `limsup_congr` / 定理 `limsup_congr`

English:
theorem limsup_congr
  statement: {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α -> β}
  proof: by
  rw [limsup_eq]
  congr with b
  exact eventually_congr (h.mono fun x hx => by simp [hx])

中文:
定理 limsup_congr
  结论: {α : 类型} [条件完备格 β] {f : 滤子 α} {u v : α -> β}
  证明: by
  rw [limsup_eq]
  congr with b
  exact eventually_congr (h.mono fun x hx => by simp [hx])

Depends on / 依赖: eventually_congr, h.mono, limsup_eq
-/
theorem limsup_congr {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α -> β}
    (h : forallᶠ a in f, u a = v a) : limsup u f = limsup v f := by
  rw [limsup_eq]
  congr with b
  exact eventually_congr (h.mono fun x hx => by simp [hx])

/--
theorem `blimsup_congr` / 定理 `blimsup_congr`

English:
theorem blimsup_congr
  given: {f : Filter β} {u v : β -> α} {p : β -> Prop} (h : forallᶠ a in f, p a -> u a = v a)
  proof: by
simpa only [blimsup_eq_limsup] using! limsup_congr eventually_inf_principal.2 h

中文:
定理 blimsup_congr
  条件: {f : 滤子 β} {u v : β -> α} {p : β -> 命题} (h : 对任意ᶠ a in f, p a -> u a = v a)
  证明: by
simpa only [blimsup_eq_limsup] using! limsup_congr eventually_inf_principal.2 h

Depends on / 依赖: blimsup_eq_limsup, eventually_inf_principal, limsup_congr
-/
theorem blimsup_congr {f : Filter β} {u v : β -> α} {p : β -> Prop} (h : forallᶠ a in f, p a -> u a = v a) :
    blimsup u f p = blimsup v f p := by
simpa only [blimsup_eq_limsup] using! limsup_congr eventually_inf_principal.2 h

/--
theorem `bliminf_congr` / 定理 `bliminf_congr`

English:
theorem bliminf_congr
  given: {f : Filter β} {u v : β -> α} {p : β -> Prop} (h : forallᶠ a in f, p a -> u a = v a)
  proof: blimsup_congr (α := αᵒᵈ) h

中文:
定理 bliminf_congr
  条件: {f : 滤子 β} {u v : β -> α} {p : β -> 命题} (h : 对任意ᶠ a in f, p a -> u a = v a)
  证明: blimsup_congr (α := αᵒᵈ) h

Depends on / 依赖: blimsup_congr
-/
theorem bliminf_congr {f : Filter β} {u v : β -> α} {p : β -> Prop} (h : forallᶠ a in f, p a -> u a = v a) :
    bliminf u f p = bliminf v f p :=
  blimsup_congr (α := αᵒᵈ) h

/--
theorem `liminf_congr` / 定理 `liminf_congr`

English:
theorem liminf_congr
  statement: {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α -> β}
  proof: limsup_congr (β := βᵒᵈ) h

@[simp]

中文:
定理 liminf_congr
  结论: {α : 类型} [条件完备格 β] {f : 滤子 α} {u v : α -> β}
  证明: limsup_congr (β := βᵒᵈ) h

@[simp]

Depends on / 依赖: limsup_congr
-/
theorem liminf_congr {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α -> β}
    (h : forallᶠ a in f, u a = v a) : liminf u f = liminf v f :=
  limsup_congr (β := βᵒᵈ) h

@[simp]
/--
theorem `limsup_const` / 定理 `limsup_const`

English:
theorem limsup_const
  statement: {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f]
  proof: by
  simpa only [limsup_eq, eventually_const] using! csInf_Ici

@[simp]

中文:
定理 limsup_const
  结论: {α : 类型} [条件完备格 β] {f : 滤子 α} [NeBot f]
  证明: by
  simpa only [limsup_eq, eventually_const] using! csInf_Ici

@[simp]

Depends on / 依赖: csInf_Ici, eventually_const, limsup_eq
-/
theorem limsup_const {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f]
    (b : β) : limsup (fun _ => b) f = b := by
  simpa only [limsup_eq, eventually_const] using! csInf_Ici

@[simp]
/--
theorem `liminf_const` / 定理 `liminf_const`

English:
theorem liminf_const
  statement: {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f]
  proof: limsup_const (β := βᵒᵈ) b

中文:
定理 liminf_const
  结论: {α : 类型} [条件完备格 β] {f : 滤子 α} [NeBot f]
  证明: limsup_const (β := βᵒᵈ) b

Depends on / 依赖: limsup_const
-/
theorem liminf_const {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f]
    (b : β) : liminf (fun _ => b) f = b :=
  limsup_const (β := βᵒᵈ) b

/--
theorem `HasBasis.liminf_eq_sSup_iUnion_iInter` / 定理 `HasBasis.liminf_eq_sSup_iUnion_iInter`

English:
theorem HasBasis.liminf_eq_sSup_iUnion_iInter
  statement: {ι ι' : Type*} {f : ι -> α} {v : Filter ι}
  proof: by
  simp_rw [liminf_eq, hv.eventually_iff]
  congr 1
  ext x
  simp only [mem_ofPred_eq, iInter_coe_set, mem_iUnion, mem_iInter, mem_Iic, Subtype.exists,
    exists_prop]

中文:
定理 有基.liminf_eq_sSup_iUnion_i整数er
  结论: {ι ι' : 类型} {f : ι -> α} {v : 滤子 ι}
  证明: by
  simp_rw [liminf_eq, hv.eventually_iff]
  congr 1
  ext x
  simp only [mem_ofPred_eq, iInter_coe_set, mem_iUnion, mem_iInter, mem_Iic, Subtype.exists,
    exists_prop]

Depends on / 依赖: Subtype, Subtype.exists, eventually_iff, exists_prop, hv.eventually_iff, iInter_coe_set, liminf_eq, mem_Iic, mem_iInter, mem_iUnion, mem_ofPred_eq, simp_rw
-/
theorem HasBasis.liminf_eq_sSup_iUnion_iInter {ι ι' : Type*} {f : ι -> α} {v : Filter ι}
    {p : ι' -> Prop} {s : ι' -> Set ι} (hv : v.HasBasis p s) :
    liminf f v = sSup (⋃ (j : Subtype p), ⋂ (i : s j), Iic (f i)) := by
  simp_rw [liminf_eq, hv.eventually_iff]
  congr 1
  ext x
  simp only [mem_ofPred_eq, iInter_coe_set, mem_iUnion, mem_iInter, mem_Iic, Subtype.exists,
    exists_prop]

/--
theorem `HasBasis.liminf_eq_sSup_univ_of_empty` / 定理 `HasBasis.liminf_eq_sSup_univ_of_empty`

English:
theorem HasBasis.liminf_eq_sSup_univ_of_empty
  statement: {f : ι -> α} {v : Filter ι}
  proof: by
  simp [hv.eq_bot_iff.2 ⟨i, hi, h'i⟩, liminf_eq]

中文:
定理 有基.liminf_eq_sSup_univ_of_empty
  结论: {f : ι -> α} {v : 滤子 ι}
  证明: by
  simp [hv.eq_bot_iff.2 ⟨i, hi, h'i⟩, liminf_eq]

Depends on / 依赖: eq_bot_iff, hv.eq_bot_iff, liminf_eq
-/
theorem HasBasis.liminf_eq_sSup_univ_of_empty {f : ι -> α} {v : Filter ι}
    {p : ι' -> Prop} {s : ι' -> Set ι} (hv : v.HasBasis p s) (i : ι') (hi : p i) (h'i : s i = ∅) :
    liminf f v = sSup univ := by
  simp [hv.eq_bot_iff.2 ⟨i, hi, h'i⟩, liminf_eq]

/--
theorem `HasBasis.limsup_eq_sInf_iUnion_iInter` / 定理 `HasBasis.limsup_eq_sInf_iUnion_iInter`

English:
theorem HasBasis.limsup_eq_sInf_iUnion_iInter
  statement: {ι ι' : Type*} {f : ι -> α} {v : Filter ι}
  proof: HasBasis.liminf_eq_sSup_iUnion_iInter (α := αᵒᵈ) hv

中文:
定理 有基.limsup_eq_sInf_iUnion_i整数er
  结论: {ι ι' : 类型} {f : ι -> α} {v : 滤子 ι}
  证明: HasBasis.liminf_eq_sSup_iUnion_iInter (α := αᵒᵈ) hv

Depends on / 依赖: HasBasis, HasBasis.liminf_eq_sSup_iUnion_iInter, liminf_eq_sSup_iUnion_iInter
-/
theorem HasBasis.limsup_eq_sInf_iUnion_iInter {ι ι' : Type*} {f : ι -> α} {v : Filter ι}
    {p : ι' -> Prop} {s : ι' -> Set ι} (hv : v.HasBasis p s) :
    limsup f v = sInf (⋃ (j : Subtype p), ⋂ (i : s j), Ici (f i)) :=
  HasBasis.liminf_eq_sSup_iUnion_iInter (α := αᵒᵈ) hv

/--
theorem `HasBasis.limsup_eq_sInf_univ_of_empty` / 定理 `HasBasis.limsup_eq_sInf_univ_of_empty`

English:
theorem HasBasis.limsup_eq_sInf_univ_of_empty
  statement: {f : ι -> α} {v : Filter ι}
  proof: HasBasis.liminf_eq_sSup_univ_of_empty (α := αᵒᵈ) hv i hi h'i

@[simp]

中文:
定理 有基.limsup_eq_sInf_univ_of_empty
  结论: {f : ι -> α} {v : 滤子 ι}
  证明: HasBasis.liminf_eq_sSup_univ_of_empty (α := αᵒᵈ) hv i hi h'i

@[simp]

Depends on / 依赖: HasBasis, HasBasis.liminf_eq_sSup_univ_of_empty, liminf_eq_sSup_univ_of_empty
-/
theorem HasBasis.limsup_eq_sInf_univ_of_empty {f : ι -> α} {v : Filter ι}
    {p : ι' -> Prop} {s : ι' -> Set ι} (hv : v.HasBasis p s) (i : ι') (hi : p i) (h'i : s i = ∅) :
    limsup f v = sInf univ :=
  HasBasis.liminf_eq_sSup_univ_of_empty (α := αᵒᵈ) hv i hi h'i

@[simp]
/--
theorem `liminf_nat_add` / 定理 `liminf_nat_add`

English:
theorem liminf_nat_add
  given: (f : Nat -> α) (k : Nat)
  proof: by
  rw [← Function.comp_def]; rw [liminf]; rw [liminf]; rw [← map_map]; rw [map_add_atTop_eq_nat]

@[simp]

中文:
定理 liminf_nat_add
  条件: (f : 自然数 -> α) (k : 自然数)
  证明: by
  rw [← Function.comp_def]; rw [liminf]; rw [liminf]; rw [← map_map]; rw [map_add_atTop_eq_nat]

@[simp]

Depends on / 依赖: Function, Function.comp_def, comp_def, liminf, map_add_atTop_eq_nat, map_map
-/
theorem liminf_nat_add (f : Nat -> α) (k : Nat) :
    liminf (fun i => f (i + k)) atTop = liminf f atTop := by
  rw [← Function.comp_def]; rw [liminf]; rw [liminf]; rw [← map_map]; rw [map_add_atTop_eq_nat]

@[simp]
/--
theorem `limsup_nat_add` / 定理 `limsup_nat_add`

English:
theorem limsup_nat_add
  given: (f : Nat -> α) (k : Nat)
  statement: limsup (fun i => f (i + k)) atTop = limsup f atTop
  proof: @liminf_nat_add αᵒᵈ _ f k

中文:
定理 limsup_nat_add
  条件: (f : 自然数 -> α) (k : 自然数)
  结论: limsup (fun i => f (i + k)) atTop = limsup f atTop
  证明: @liminf_nat_add αᵒᵈ _ f k

Depends on / 依赖: liminf_nat_add
-/
theorem limsup_nat_add (f : Nat -> α) (k : Nat) : limsup (fun i => f (i + k)) atTop = limsup f atTop :=
  @liminf_nat_add αᵒᵈ _ f k

variable {f : Filter ι} {u : ι -> α} {a : α}

/--
lemma `le_limsup_of_frequently_le` / 引理 `le_limsup_of_frequently_le`

English:
lemma le_limsup_of_frequently_le
  statement: (hu : existsᶠ i in f, a <= u i)
  proof: by
  refine le_limsup_of_le hu_le fun b hb => ?_
  obtain ⟨n, han, hnb⟩ := (hu.and_eventually hb).exists
  exact han.trans hnb

中文:
引理 le_limsup_of_frequently_le
  结论: (hu : 存在ᶠ i in f, a <= u i)
  证明: by
  refine le_limsup_of_le hu_le fun b hb => ?_
  obtain ⟨n, han, hnb⟩ := (hu.and_eventually hb).exists
  exact han.trans hnb

Depends on / 依赖: and_eventually, han.trans, hu.and_eventually, hu_le, isBoundedDefault, le_limsup_of_le, limsup
-/
lemma le_limsup_of_frequently_le (hu : existsᶠ i in f, a <= u i)
    (hu_le : f.IsBoundedUnder (· <= ·) u := by isBoundedDefault) : a <= limsup u f := by
  refine le_limsup_of_le hu_le fun b hb => ?_
  obtain ⟨n, han, hnb⟩ := (hu.and_eventually hb).exists
  exact han.trans hnb

/--
lemma `liminf_le_of_frequently_le` / 引理 `liminf_le_of_frequently_le`

English:
lemma liminf_le_of_frequently_le
  statement: (hu : existsᶠ i in f, u i <= a)
  proof: by
  refine liminf_le_of_le hu_le fun b hb => ?_
  obtain ⟨n, hna, hbn⟩ := (hu.and_eventually hb).exists
  exact hbn.trans hna

中文:
引理 liminf_le_of_frequently_le
  结论: (hu : 存在ᶠ i in f, u i <= a)
  证明: by
  refine liminf_le_of_le hu_le fun b hb => ?_
  obtain ⟨n, hna, hbn⟩ := (hu.and_eventually hb).exists
  exact hbn.trans hna

Depends on / 依赖: and_eventually, hbn.trans, hu.and_eventually, hu_le, isBoundedDefault, liminf, liminf_le_of_le
-/
lemma liminf_le_of_frequently_le (hu : existsᶠ i in f, u i <= a)
    (hu_le : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault) : liminf u f <= a := by
  refine liminf_le_of_le hu_le fun b hb => ?_
  obtain ⟨n, hna, hbn⟩ := (hu.and_eventually hb).exists
  exact hbn.trans hna

end ConditionallyCompleteLattice

section CompleteLattice

variable [CompleteLattice α]

@[simp]
/--
theorem `limsSup_bot` / 定理 `limsSup_bot`

English:
theorem limsSup_bot
  statement: limsSup (⊥ : Filter α) = ⊥
  proof: bot_unique sInf_le by simp

中文:
定理 limsSup_bot
  结论: limsSup (⊥ : 滤子 α) = ⊥
  证明: bot_unique sInf_le by simp

Depends on / 依赖: bot_unique, sInf_le
-/
theorem limsSup_bot : limsSup (⊥ : Filter α) = ⊥ :=
bot_unique sInf_le by simp

/--
theorem `limsup_bot` / 定理 `limsup_bot`

English:
theorem limsup_bot
  given: (f : β -> α)
  statement: limsup f ⊥ = ⊥
  proof: by simp [limsup]

@[simp]

中文:
定理 limsup_bot
  条件: (f : β -> α)
  结论: limsup f ⊥ = ⊥
  证明: by simp [limsup]

@[simp]
-/
@[simp] theorem limsup_bot (f : β -> α) : limsup f ⊥ = ⊥ := by simp [limsup]

@[simp]
/--
theorem `limsInf_bot` / 定理 `limsInf_bot`

English:
theorem limsInf_bot
  statement: limsInf (⊥ : Filter α) = ⊤
  proof: top_unique le_sSup by simp

中文:
定理 limsInf_bot
  结论: limsInf (⊥ : 滤子 α) = ⊤
  证明: top_unique le_sSup by simp

Depends on / 依赖: le_sSup, top_unique
-/
theorem limsInf_bot : limsInf (⊥ : Filter α) = ⊤ :=
top_unique le_sSup by simp

/--
theorem `liminf_bot` / 定理 `liminf_bot`

English:
theorem liminf_bot
  given: (f : β -> α)
  statement: liminf f ⊥ = ⊤
  proof: by simp [liminf]

@[simp]

中文:
定理 liminf_bot
  条件: (f : β -> α)
  结论: liminf f ⊥ = ⊤
  证明: by simp [liminf]

@[simp]
-/
@[simp] theorem liminf_bot (f : β -> α) : liminf f ⊥ = ⊤ := by simp [liminf]

@[simp]
/--
theorem `limsSup_top` / 定理 `limsSup_top`

English:
theorem limsSup_top
  statement: limsSup (⊤ : Filter α) = ⊤
  proof: top_unique le_sInf by simpa [eq_univ_iff_forall] using fun b hb => top_unique hb _

@[simp]

中文:
定理 limsSup_top
  结论: limsSup (⊤ : 滤子 α) = ⊤
  证明: top_unique le_sInf by simpa [eq_univ_iff_forall] using fun b hb => top_unique hb _

@[simp]

Depends on / 依赖: eq_univ_iff_forall, le_sInf, top_unique
-/
theorem limsSup_top : limsSup (⊤ : Filter α) = ⊤ :=
top_unique le_sInf by simpa [eq_univ_iff_forall] using fun b hb => top_unique hb _

@[simp]
/--
theorem `limsInf_top` / 定理 `limsInf_top`

English:
theorem limsInf_top
  statement: limsInf (⊤ : Filter α) = ⊥
  proof: bot_unique sSup_le by simpa [eq_univ_iff_forall] using fun b hb => bot_unique hb _

@[simp]

中文:
定理 limsInf_top
  结论: limsInf (⊤ : 滤子 α) = ⊥
  证明: bot_unique sSup_le by simpa [eq_univ_iff_forall] using fun b hb => bot_unique hb _

@[simp]

Depends on / 依赖: bot_unique, eq_univ_iff_forall, sSup_le
-/
theorem limsInf_top : limsInf (⊤ : Filter α) = ⊥ :=
bot_unique sSup_le by simpa [eq_univ_iff_forall] using fun b hb => bot_unique hb _

@[simp]
/--
theorem `blimsup_false` / 定理 `blimsup_false`

English:
theorem blimsup_false
  given: {f : Filter β} {u : β -> α}
  statement: (blimsup u f fun _ => False) = ⊥
  proof: by
  simp [blimsup_eq]

@[simp]

中文:
定理 blimsup_false
  条件: {f : 滤子 β} {u : β -> α}
  结论: (blimsup u f fun _ => 假) = ⊥
  证明: by
  simp [blimsup_eq]

@[simp]

Depends on / 依赖: blimsup_eq
-/
theorem blimsup_false {f : Filter β} {u : β -> α} : (blimsup u f fun _ => False) = ⊥ := by
  simp [blimsup_eq]

@[simp]
/--
theorem `bliminf_false` / 定理 `bliminf_false`

English:
theorem bliminf_false
  given: {f : Filter β} {u : β -> α}
  statement: (bliminf u f fun _ => False) = ⊤
  proof: by
  simp [bliminf_eq]

中文:
定理 bliminf_false
  条件: {f : 滤子 β} {u : β -> α}
  结论: (bliminf u f fun _ => 假) = ⊤
  证明: by
  simp [bliminf_eq]

Depends on / 依赖: bliminf_eq
-/
theorem bliminf_false {f : Filter β} {u : β -> α} : (bliminf u f fun _ => False) = ⊤ := by
  simp [bliminf_eq]

/-- Same as `limsup_const` applied to `⊥` but without the `NeBot f` assumption -/
@[simp]
/--
theorem `limsup_const_bot` / 定理 `limsup_const_bot`

English:
theorem limsup_const_bot
  given: {f : Filter β}
  statement: limsup (fun _ : β => (⊥ : α)) f = (⊥ : α)
  proof: by
  rw [limsup_eq]; rw [eq_bot_iff]
  exact sInf_le (Eventually.of_forall fun _ => le_rfl)

中文:
定理 limsup_const_bot
  条件: {f : 滤子 β}
  结论: limsup (fun _ : β => (⊥ : α)) f = (⊥ : α)
  证明: by
  rw [limsup_eq]; rw [eq_bot_iff]
  exact sInf_le (Eventually.of_forall fun _ => le_rfl)

Depends on / 依赖: Eventually, Eventually.of_forall, eq_bot_iff, le_rfl, limsup_eq, of_forall, sInf_le
-/
theorem limsup_const_bot {f : Filter β} : limsup (fun _ : β => (⊥ : α)) f = (⊥ : α) := by
  rw [limsup_eq]; rw [eq_bot_iff]
  exact sInf_le (Eventually.of_forall fun _ => le_rfl)

/-- Same as `limsup_const` applied to `⊤` but without the `NeBot f` assumption -/
@[simp]
/--
theorem `liminf_const_top` / 定理 `liminf_const_top`

English:
theorem liminf_const_top
  given: {f : Filter β}
  statement: liminf (fun _ : β => (⊤ : α)) f = (⊤ : α)
  proof: limsup_const_bot (α := αᵒᵈ)

中文:
定理 liminf_const_top
  条件: {f : 滤子 β}
  结论: liminf (fun _ : β => (⊤ : α)) f = (⊤ : α)
  证明: limsup_const_bot (α := αᵒᵈ)

Depends on / 依赖: limsup_const_bot
-/
theorem liminf_const_top {f : Filter β} : liminf (fun _ : β => (⊤ : α)) f = (⊤ : α) :=
  limsup_const_bot (α := αᵒᵈ)

/--
theorem `HasBasis.limsSup_eq_iInf_sSup` / 定理 `HasBasis.limsSup_eq_iInf_sSup`

English:
theorem HasBasis.limsSup_eq_iInf_sSup
  given: {ι} {p : ι -> Prop} {s} {f : Filter α} (h : f.HasBasis p s)
  proof: le_antisymm (le_iInf₂ fun i hi => sInf_le <| h.eventually_iff.2 ⟨i, hi, fun _ => le_sSup⟩)
    (le_sInf fun _ ha =>
      let ⟨_, hi, ha⟩ := h.eventually_iff.1 ha
iInf₂_le_of_le _ hi sSup_le ha)

中文:
定理 有基.limsSup_eq_iInf_sSup
  条件: {ι} {p : ι -> 命题} {s} {f : 滤子 α} (h : f.有基 p s)
  证明: le_antisymm (le_iInf₂ fun i hi => sInf_le <| h.eventually_iff.2 ⟨i, hi, fun _ => le_sSup⟩)
    (le_sInf fun _ ha =>
      let ⟨_, hi, ha⟩ := h.eventually_iff.1 ha
iInf₂_le_of_le _ hi sSup_le ha)

Depends on / 依赖: eventually_iff, h.eventually_iff, le_antisymm, le_sInf, le_sSup, sInf_le, sSup_le
-/
theorem HasBasis.limsSup_eq_iInf_sSup {ι} {p : ι -> Prop} {s} {f : Filter α} (h : f.HasBasis p s) :
    limsSup f = ⨅ (i) (_ : p i), sSup (s i) :=
  le_antisymm (le_iInf₂ fun i hi => sInf_le <| h.eventually_iff.2 ⟨i, hi, fun _ => le_sSup⟩)
    (le_sInf fun _ ha =>
      let ⟨_, hi, ha⟩ := h.eventually_iff.1 ha
iInf₂_le_of_le _ hi sSup_le ha)

/--
theorem `HasBasis.limsInf_eq_iSup_sInf` / 定理 `HasBasis.limsInf_eq_iSup_sInf`

English:
theorem HasBasis.limsInf_eq_iSup_sInf
  statement: {p : ι -> Prop} {s : ι -> Set α} {f : Filter α}
  proof: HasBasis.limsSup_eq_iInf_sSup (α := αᵒᵈ) h

中文:
定理 有基.limsInf_eq_iSup_sInf
  结论: {p : ι -> 命题} {s : ι -> 集合 α} {f : 滤子 α}
  证明: HasBasis.limsSup_eq_iInf_sSup (α := αᵒᵈ) h

Depends on / 依赖: HasBasis, HasBasis.limsSup_eq_iInf_sSup, limsSup_eq_iInf_sSup
-/
theorem HasBasis.limsInf_eq_iSup_sInf {p : ι -> Prop} {s : ι -> Set α} {f : Filter α}
    (h : f.HasBasis p s) : limsInf f = ⨆ (i) (_ : p i), sInf (s i) :=
  HasBasis.limsSup_eq_iInf_sSup (α := αᵒᵈ) h

/--
theorem `limsSup_eq_iInf_sSup` / 定理 `limsSup_eq_iInf_sSup`

English:
theorem limsSup_eq_iInf_sSup
  given: {f : Filter α}
  statement: limsSup f = ⨅ s in f, sSup s
  proof: f.basis_sets.limsSup_eq_iInf_sSup

中文:
定理 limsSup_eq_iInf_sSup
  条件: {f : 滤子 α}
  结论: limsSup f = ⨅ s in f, sSup s
  证明: f.basis_sets.limsSup_eq_iInf_sSup

Depends on / 依赖: basis_sets, f.basis_sets.limsSup_eq_iInf_sSup, limsSup_eq_iInf_sSup
-/
theorem limsSup_eq_iInf_sSup {f : Filter α} : limsSup f = ⨅ s in f, sSup s :=
  f.basis_sets.limsSup_eq_iInf_sSup

/--
theorem `limsInf_eq_iSup_sInf` / 定理 `limsInf_eq_iSup_sInf`

English:
theorem limsInf_eq_iSup_sInf
  given: {f : Filter α}
  statement: limsInf f = ⨆ s in f, sInf s
  proof: limsSup_eq_iInf_sSup (α := αᵒᵈ)

中文:
定理 limsInf_eq_iSup_sInf
  条件: {f : 滤子 α}
  结论: limsInf f = ⨆ s in f, sInf s
  证明: limsSup_eq_iInf_sSup (α := αᵒᵈ)

Depends on / 依赖: limsSup_eq_iInf_sSup
-/
theorem limsInf_eq_iSup_sInf {f : Filter α} : limsInf f = ⨆ s in f, sInf s :=
  limsSup_eq_iInf_sSup (α := αᵒᵈ)

/--
theorem `limsup_le_iSup` / 定理 `limsup_le_iSup`

English:
theorem limsup_le_iSup
  given: {f : Filter β} {u : β -> α}
  statement: limsup u f <= ⨆ n, u n
  proof: limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall (le_iSup u))

中文:
定理 limsup_le_iSup
  条件: {f : 滤子 β} {u : β -> α}
  结论: limsup u f <= ⨆ n, u n
  证明: limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall (le_iSup u))

Depends on / 依赖: Eventually, Eventually.of_forall, isBoundedDefault, le_iSup, limsup_le_of_le, of_forall
-/
theorem limsup_le_iSup {f : Filter β} {u : β -> α} : limsup u f <= ⨆ n, u n :=
  limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall (le_iSup u))

/--
theorem `iInf_le_liminf` / 定理 `iInf_le_liminf`

English:
theorem iInf_le_liminf
  given: {f : Filter β} {u : β -> α}
  statement: ⨅ n, u n <= liminf u f
  proof: le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall (iInf_le u))

中文:
定理 iInf_le_liminf
  条件: {f : 滤子 β} {u : β -> α}
  结论: ⨅ n, u n <= liminf u f
  证明: le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall (iInf_le u))

Depends on / 依赖: Eventually, Eventually.of_forall, iInf_le, isBoundedDefault, le_liminf_of_le, of_forall
-/
theorem iInf_le_liminf {f : Filter β} {u : β -> α} : ⨅ n, u n <= liminf u f :=
  le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall (iInf_le u))

/--
theorem `limsup_eq_iInf_iSup` / 定理 `limsup_eq_iInf_iSup`

English:
theorem limsup_eq_iInf_iSup
  given: {f : Filter β} {u : β -> α}
  statement: limsup u f = ⨅ s in f, ⨆ a in s, u a
  proof: (f.basis_sets.map u).limsSup_eq_iInf_sSup.trans by simp only [sSup_image, id]

中文:
定理 limsup_eq_iInf_iSup
  条件: {f : 滤子 β} {u : β -> α}
  结论: limsup u f = ⨅ s in f, ⨆ a in s, u a
  证明: (f.basis_sets.map u).limsSup_eq_iInf_sSup.trans by simp only [sSup_image, id]

Depends on / 依赖: basis_sets, f.basis_sets.map, limsSup_eq_iInf_sSup, limsSup_eq_iInf_sSup.trans, sSup_image
-/
theorem limsup_eq_iInf_iSup {f : Filter β} {u : β -> α} : limsup u f = ⨅ s in f, ⨆ a in s, u a :=
(f.basis_sets.map u).limsSup_eq_iInf_sSup.trans by simp only [sSup_image, id]

/--
theorem `limsup_eq_iInf_iSup_of_nat` / 定理 `limsup_eq_iInf_iSup_of_nat`

English:
theorem limsup_eq_iInf_iSup_of_nat
  given: {u : Nat -> α}
  statement: limsup u atTop = ⨅ n : Nat, ⨆ i >= n, u i
  proof: (atTop_basis.map u).limsSup_eq_iInf_sSup.trans by simp only [sSup_image, iInf_const]; rfl

中文:
定理 limsup_eq_iInf_iSup_of_nat
  条件: {u : 自然数 -> α}
  结论: limsup u atTop = ⨅ n : 自然数, ⨆ i >= n, u i
  证明: (atTop_basis.map u).limsSup_eq_iInf_sSup.trans by simp only [sSup_image, iInf_const]; rfl

Depends on / 依赖: atTop_basis, atTop_basis.map, iInf_const, limsSup_eq_iInf_sSup, limsSup_eq_iInf_sSup.trans, sSup_image
-/
theorem limsup_eq_iInf_iSup_of_nat {u : Nat -> α} : limsup u atTop = ⨅ n : Nat, ⨆ i >= n, u i :=
(atTop_basis.map u).limsSup_eq_iInf_sSup.trans by simp only [sSup_image, iInf_const]; rfl

/--
theorem `limsup_eq_iInf_iSup_of_nat'` / 定理 `limsup_eq_iInf_iSup_of_nat'`

English:
theorem limsup_eq_iInf_iSup_of_nat'
  given: {u : Nat -> α}
  statement: limsup u atTop = ⨅ n : Nat, ⨆ i : Nat, u (i + n)
  proof: by
  simp only [limsup_eq_iInf_iSup_of_nat, iSup_ge_eq_iSup_nat_add]

中文:
定理 limsup_eq_iInf_iSup_of_nat'
  条件: {u : 自然数 -> α}
  结论: limsup u atTop = ⨅ n : 自然数, ⨆ i : 自然数, u (i + n)
  证明: by
  simp only [limsup_eq_iInf_iSup_of_nat, iSup_ge_eq_iSup_nat_add]

Depends on / 依赖: iSup_ge_eq_iSup_nat_add, limsup_eq_iInf_iSup_of_nat
-/
theorem limsup_eq_iInf_iSup_of_nat' {u : Nat -> α} : limsup u atTop = ⨅ n : Nat, ⨆ i : Nat, u (i + n) := by
  simp only [limsup_eq_iInf_iSup_of_nat, iSup_ge_eq_iSup_nat_add]

/--
theorem `HasBasis.limsup_eq_iInf_iSup` / 定理 `HasBasis.limsup_eq_iInf_iSup`

English:
theorem HasBasis.limsup_eq_iInf_iSup
  statement: {p : ι -> Prop} {s : ι -> Set β} {f : Filter β} {u : β -> α}
  proof: (h.map u).limsSup_eq_iInf_sSup.trans by simp only [sSup_image]

中文:
定理 有基.limsup_eq_iInf_iSup
  结论: {p : ι -> 命题} {s : ι -> 集合 β} {f : 滤子 β} {u : β -> α}
  证明: (h.map u).limsSup_eq_iInf_sSup.trans by simp only [sSup_image]

Depends on / 依赖: h.map, limsSup_eq_iInf_sSup, limsSup_eq_iInf_sSup.trans, sSup_image
-/
theorem HasBasis.limsup_eq_iInf_iSup {p : ι -> Prop} {s : ι -> Set β} {f : Filter β} {u : β -> α}
    (h : f.HasBasis p s) : limsup u f = ⨅ (i) (_ : p i), ⨆ a in s i, u a :=
(h.map u).limsSup_eq_iInf_sSup.trans by simp only [sSup_image]

/--
lemma `limsSup_principal_eq_sSup` / 引理 `limsSup_principal_eq_sSup`

English:
lemma limsSup_principal_eq_sSup
  given: (s : Set α)
  statement: limsSup (𝓟 s) = sSup s
  proof: by
  simpa only [limsSup, eventually_principal] using! sInf_upperBounds_eq_sSup s

中文:
引理 limsSup_principal_eq_sSup
  条件: (s : 集合 α)
  结论: limsSup (𝓟 s) = sSup s
  证明: by
  simpa only [limsSup, eventually_principal] using! sInf_upperBounds_eq_sSup s

Depends on / 依赖: eventually_principal, limsSup, sInf_upperBounds_eq_sSup
-/
lemma limsSup_principal_eq_sSup (s : Set α) : limsSup (𝓟 s) = sSup s := by
  simpa only [limsSup, eventually_principal] using! sInf_upperBounds_eq_sSup s

/--
lemma `limsInf_principal_eq_sInf` / 引理 `limsInf_principal_eq_sInf`

English:
lemma limsInf_principal_eq_sInf
  given: (s : Set α)
  statement: limsInf (𝓟 s) = sInf s
  proof: by
  simpa only [limsInf, eventually_principal] using! sSup_lowerBounds_eq_sInf s

中文:
引理 limsInf_principal_eq_sInf
  条件: (s : 集合 α)
  结论: limsInf (𝓟 s) = sInf s
  证明: by
  simpa only [limsInf, eventually_principal] using! sSup_lowerBounds_eq_sInf s

Depends on / 依赖: eventually_principal, limsInf, sSup_lowerBounds_eq_sInf
-/
lemma limsInf_principal_eq_sInf (s : Set α) : limsInf (𝓟 s) = sInf s := by
  simpa only [limsInf, eventually_principal] using! sSup_lowerBounds_eq_sInf s

/--
lemma `limsup_top_eq_iSup` / 引理 `limsup_top_eq_iSup`

English:
lemma limsup_top_eq_iSup
  given: (u : β -> α)
  statement: limsup u ⊤ = ⨆ i, u i
  proof: by
  rw [limsup]; rw [map_top]; rw [limsSup_principal_eq_sSup]; rw [sSup_range]

中文:
引理 limsup_top_eq_iSup
  条件: (u : β -> α)
  结论: limsup u ⊤ = ⨆ i, u i
  证明: by
  rw [limsup]; rw [map_top]; rw [limsSup_principal_eq_sSup]; rw [sSup_range]
-/
@[simp] lemma limsup_top_eq_iSup (u : β -> α) : limsup u ⊤ = ⨆ i, u i := by
  rw [limsup]; rw [map_top]; rw [limsSup_principal_eq_sSup]; rw [sSup_range]

/--
lemma `liminf_top_eq_iInf` / 引理 `liminf_top_eq_iInf`

English:
lemma liminf_top_eq_iInf
  given: (u : β -> α)
  statement: liminf u ⊤ = ⨅ i, u i
  proof: by
  rw [liminf]; rw [map_top]; rw [limsInf_principal_eq_sInf]; rw [sInf_range]

中文:
引理 liminf_top_eq_iInf
  条件: (u : β -> α)
  结论: liminf u ⊤ = ⨅ i, u i
  证明: by
  rw [liminf]; rw [map_top]; rw [limsInf_principal_eq_sInf]; rw [sInf_range]
-/
@[simp] lemma liminf_top_eq_iInf (u : β -> α) : liminf u ⊤ = ⨅ i, u i := by
  rw [liminf]; rw [map_top]; rw [limsInf_principal_eq_sInf]; rw [sInf_range]

/--
theorem `blimsup_congr'` / 定理 `blimsup_congr'`

English:
theorem blimsup_congr'
  statement: {f : Filter β} {p q : β -> Prop} {u : β -> α}
  proof: by
  simp only [blimsup_eq]
  congr with a
  refine eventually_congr (h.mono fun b hb => ?_)
  rcases eq_or_ne (u b) ⊥ with hu | hu; · simp [hu]
  rw [hb hu]

中文:
定理 blimsup_congr'
  结论: {f : 滤子 β} {p q : β -> 命题} {u : β -> α}
  证明: by
  simp only [blimsup_eq]
  congr with a
  refine eventually_congr (h.mono fun b hb => ?_)
  rcases eq_or_ne (u b) ⊥ with hu | hu; · simp [hu]
  rw [hb hu]

Depends on / 依赖: blimsup_eq, eq_or_ne, eventually_congr, h.mono
-/
theorem blimsup_congr' {f : Filter β} {p q : β -> Prop} {u : β -> α}
    (h : forallᶠ x in f, u x != ⊥ -> (p x ↔ q x)) : blimsup u f p = blimsup u f q := by
  simp only [blimsup_eq]
  congr with a
  refine eventually_congr (h.mono fun b hb => ?_)
  rcases eq_or_ne (u b) ⊥ with hu | hu; · simp [hu]
  rw [hb hu]

/--
theorem `bliminf_congr'` / 定理 `bliminf_congr'`

English:
theorem bliminf_congr'
  statement: {f : Filter β} {p q : β -> Prop} {u : β -> α}
  proof: blimsup_congr' (α := αᵒᵈ) h

中文:
定理 bliminf_congr'
  结论: {f : 滤子 β} {p q : β -> 命题} {u : β -> α}
  证明: blimsup_congr' (α := αᵒᵈ) h

Depends on / 依赖: blimsup_congr
-/
theorem bliminf_congr' {f : Filter β} {p q : β -> Prop} {u : β -> α}
    (h : forallᶠ x in f, u x != ⊤ -> (p x ↔ q x)) : bliminf u f p = bliminf u f q :=
  blimsup_congr' (α := αᵒᵈ) h

set_option backward.isDefEq.respectTransparency false in
/--
lemma `HasBasis.blimsup_eq_iInf_iSup` / 引理 `HasBasis.blimsup_eq_iInf_iSup`

English:
lemma HasBasis.blimsup_eq_iInf_iSup
  statement: {p : ι -> Prop} {s : ι -> Set β} {f : Filter β} {u : β -> α}
  proof: by
  simp only [blimsup_eq_limsup, (hf.inf_principal _).limsup_eq_iInf_iSup, mem_inter_iff, iSup_and,
    mem_ofPred_eq]

中文:
引理 有基.blimsup_eq_iInf_iSup
  结论: {p : ι -> 命题} {s : ι -> 集合 β} {f : 滤子 β} {u : β -> α}
  证明: by
  simp only [blimsup_eq_limsup, (hf.inf_principal _).limsup_eq_iInf_iSup, mem_inter_iff, iSup_and,
    mem_ofPred_eq]

Depends on / 依赖: blimsup_eq_limsup, hf.inf_principal, iSup_and, inf_principal, limsup_eq_iInf_iSup, mem_inter_iff, mem_ofPred_eq
-/
lemma HasBasis.blimsup_eq_iInf_iSup {p : ι -> Prop} {s : ι -> Set β} {f : Filter β} {u : β -> α}
    (hf : f.HasBasis p s) {q : β -> Prop} :
    blimsup u f q = ⨅ (i) (_ : p i), ⨆ a in s i, ⨆ (_ : q a), u a := by
  simp only [blimsup_eq_limsup, (hf.inf_principal _).limsup_eq_iInf_iSup, mem_inter_iff, iSup_and,
    mem_ofPred_eq]

/--
theorem `blimsup_eq_iInf_biSup` / 定理 `blimsup_eq_iInf_biSup`

English:
theorem blimsup_eq_iInf_biSup
  given: {f : Filter β} {p : β -> Prop} {u : β -> α}
  proof: by
  simp only [f.basis_sets.blimsup_eq_iInf_iSup, iSup_and', id, and_comm]

中文:
定理 blimsup_eq_iInf_biSup
  条件: {f : 滤子 β} {p : β -> 命题} {u : β -> α}
  证明: by
  simp only [f.basis_sets.blimsup_eq_iInf_iSup, iSup_and', id, and_comm]

Depends on / 依赖: and_comm, basis_sets, blimsup_eq_iInf_iSup, f.basis_sets.blimsup_eq_iInf_iSup, iSup_and
-/
theorem blimsup_eq_iInf_biSup {f : Filter β} {p : β -> Prop} {u : β -> α} :
    blimsup u f p = ⨅ s in f, ⨆ (b) (_ : p b ∧ b in s), u b := by
  simp only [f.basis_sets.blimsup_eq_iInf_iSup, iSup_and', id, and_comm]

/--
theorem `blimsup_eq_iInf_biSup_of_nat` / 定理 `blimsup_eq_iInf_biSup_of_nat`

English:
theorem blimsup_eq_iInf_biSup_of_nat
  given: {p : Nat -> Prop} {u : Nat -> α}
  proof: by
  simp only [atTop_basis.blimsup_eq_iInf_iSup, @and_comm (p _), iSup_and, mem_Ici, iInf_true]

中文:
定理 blimsup_eq_iInf_biSup_of_nat
  条件: {p : 自然数 -> 命题} {u : 自然数 -> α}
  证明: by
  simp only [atTop_basis.blimsup_eq_iInf_iSup, @and_comm (p _), iSup_and, mem_Ici, iInf_true]

Depends on / 依赖: and_comm, atTop_basis, atTop_basis.blimsup_eq_iInf_iSup, blimsup_eq_iInf_iSup, iInf_true, iSup_and, mem_Ici
-/
theorem blimsup_eq_iInf_biSup_of_nat {p : Nat -> Prop} {u : Nat -> α} :
    blimsup u atTop p = ⨅ i, ⨆ (j) (_ : p j ∧ i <= j), u j := by
  simp only [atTop_basis.blimsup_eq_iInf_iSup, @and_comm (p _), iSup_and, mem_Ici, iInf_true]

/--
theorem `liminf_eq_iSup_iInf` / 定理 `liminf_eq_iSup_iInf`

English:
theorem liminf_eq_iSup_iInf
  given: {f : Filter β} {u : β -> α}
  statement: liminf u f = ⨆ s in f, ⨅ a in s, u a
  proof: limsup_eq_iInf_iSup (α := αᵒᵈ)

中文:
定理 liminf_eq_iSup_iInf
  条件: {f : 滤子 β} {u : β -> α}
  结论: liminf u f = ⨆ s in f, ⨅ a in s, u a
  证明: limsup_eq_iInf_iSup (α := αᵒᵈ)

Depends on / 依赖: limsup_eq_iInf_iSup
-/
theorem liminf_eq_iSup_iInf {f : Filter β} {u : β -> α} : liminf u f = ⨆ s in f, ⨅ a in s, u a :=
  limsup_eq_iInf_iSup (α := αᵒᵈ)

/--
theorem `liminf_eq_iSup_iInf_of_nat` / 定理 `liminf_eq_iSup_iInf_of_nat`

English:
theorem liminf_eq_iSup_iInf_of_nat
  given: {u : Nat -> α}
  statement: liminf u atTop = ⨆ n : Nat, ⨅ i >= n, u i
  proof: @limsup_eq_iInf_iSup_of_nat αᵒᵈ _ u

中文:
定理 liminf_eq_iSup_iInf_of_nat
  条件: {u : 自然数 -> α}
  结论: liminf u atTop = ⨆ n : 自然数, ⨅ i >= n, u i
  证明: @limsup_eq_iInf_iSup_of_nat αᵒᵈ _ u

Depends on / 依赖: limsup_eq_iInf_iSup_of_nat
-/
theorem liminf_eq_iSup_iInf_of_nat {u : Nat -> α} : liminf u atTop = ⨆ n : Nat, ⨅ i >= n, u i :=
  @limsup_eq_iInf_iSup_of_nat αᵒᵈ _ u

/--
theorem `liminf_eq_iSup_iInf_of_nat'` / 定理 `liminf_eq_iSup_iInf_of_nat'`

English:
theorem liminf_eq_iSup_iInf_of_nat'
  given: {u : Nat -> α}
  statement: liminf u atTop = ⨆ n : Nat, ⨅ i : Nat, u (i + n)
  proof: @limsup_eq_iInf_iSup_of_nat' αᵒᵈ _ _

中文:
定理 liminf_eq_iSup_iInf_of_nat'
  条件: {u : 自然数 -> α}
  结论: liminf u atTop = ⨆ n : 自然数, ⨅ i : 自然数, u (i + n)
  证明: @limsup_eq_iInf_iSup_of_nat' αᵒᵈ _ _

Depends on / 依赖: limsup_eq_iInf_iSup_of_nat
-/
theorem liminf_eq_iSup_iInf_of_nat' {u : Nat -> α} : liminf u atTop = ⨆ n : Nat, ⨅ i : Nat, u (i + n) :=
  @limsup_eq_iInf_iSup_of_nat' αᵒᵈ _ _

/--
theorem `HasBasis.liminf_eq_iSup_iInf` / 定理 `HasBasis.liminf_eq_iSup_iInf`

English:
theorem HasBasis.liminf_eq_iSup_iInf
  statement: {p : ι -> Prop} {s : ι -> Set β} {f : Filter β} {u : β -> α}
  proof: HasBasis.limsup_eq_iInf_iSup (α := αᵒᵈ) h

中文:
定理 有基.liminf_eq_iSup_iInf
  结论: {p : ι -> 命题} {s : ι -> 集合 β} {f : 滤子 β} {u : β -> α}
  证明: HasBasis.limsup_eq_iInf_iSup (α := αᵒᵈ) h

Depends on / 依赖: HasBasis, HasBasis.limsup_eq_iInf_iSup, limsup_eq_iInf_iSup
-/
theorem HasBasis.liminf_eq_iSup_iInf {p : ι -> Prop} {s : ι -> Set β} {f : Filter β} {u : β -> α}
    (h : f.HasBasis p s) : liminf u f = ⨆ (i) (_ : p i), ⨅ a in s i, u a :=
  HasBasis.limsup_eq_iInf_iSup (α := αᵒᵈ) h

/--
theorem `bliminf_eq_iSup_biInf` / 定理 `bliminf_eq_iSup_biInf`

English:
theorem bliminf_eq_iSup_biInf
  given: {f : Filter β} {p : β -> Prop} {u : β -> α}
  proof: @blimsup_eq_iInf_biSup αᵒᵈ β _ f p u

中文:
定理 bliminf_eq_iSup_biInf
  条件: {f : 滤子 β} {p : β -> 命题} {u : β -> α}
  证明: @blimsup_eq_iInf_biSup αᵒᵈ β _ f p u

Depends on / 依赖: blimsup_eq_iInf_biSup
-/
theorem bliminf_eq_iSup_biInf {f : Filter β} {p : β -> Prop} {u : β -> α} :
    bliminf u f p = ⨆ s in f, ⨅ (b) (_ : p b ∧ b in s), u b :=
  @blimsup_eq_iInf_biSup αᵒᵈ β _ f p u

/--
theorem `bliminf_eq_iSup_biInf_of_nat` / 定理 `bliminf_eq_iSup_biInf_of_nat`

English:
theorem bliminf_eq_iSup_biInf_of_nat
  given: {p : Nat -> Prop} {u : Nat -> α}
  proof: @blimsup_eq_iInf_biSup_of_nat αᵒᵈ _ p u

中文:
定理 bliminf_eq_iSup_biInf_of_nat
  条件: {p : 自然数 -> 命题} {u : 自然数 -> α}
  证明: @blimsup_eq_iInf_biSup_of_nat αᵒᵈ _ p u

Depends on / 依赖: blimsup_eq_iInf_biSup_of_nat
-/
theorem bliminf_eq_iSup_biInf_of_nat {p : Nat -> Prop} {u : Nat -> α} :
    bliminf u atTop p = ⨆ i, ⨅ (j) (_ : p j ∧ i <= j), u j :=
  @blimsup_eq_iInf_biSup_of_nat αᵒᵈ _ p u

/--
theorem `iSup_liminf_le_liminf_iSup` / 定理 `iSup_liminf_le_liminf_iSup`

English:
theorem iSup_liminf_le_liminf_iSup
  given: {f : Filter β} {u : ι -> β -> α}
  proof: iSup_le fun i => liminf_le_liminf .of_forall fun b => le_iSup (u · b) i

中文:
定理 iSup_liminf_le_liminf_iSup
  条件: {f : 滤子 β} {u : ι -> β -> α}
  证明: iSup_le fun i => liminf_le_liminf .of_forall fun b => le_iSup (u · b) i

Depends on / 依赖: iSup_le, le_iSup, liminf_le_liminf, of_forall
-/
theorem iSup_liminf_le_liminf_iSup {f : Filter β} {u : ι -> β -> α} :
    ⨆ i, liminf (u i) f <= liminf (fun b => ⨆ i, u i b) f :=
iSup_le fun i => liminf_le_liminf .of_forall fun b => le_iSup (u · b) i

/--
theorem `limsup_iInf_le_iInf_limsup` / 定理 `limsup_iInf_le_iInf_limsup`

English:
theorem limsup_iInf_le_iInf_limsup
  given: {f : Filter β} {u : ι -> β -> α}
  proof: iSup_liminf_le_liminf_iSup (α := αᵒᵈ)

中文:
定理 limsup_iInf_le_iInf_limsup
  条件: {f : 滤子 β} {u : ι -> β -> α}
  证明: iSup_liminf_le_liminf_iSup (α := αᵒᵈ)

Depends on / 依赖: iSup_liminf_le_liminf_iSup
-/
theorem limsup_iInf_le_iInf_limsup {f : Filter β} {u : ι -> β -> α} :
    limsup (fun b => ⨅ i, u i b) f <= ⨅ i, limsup (u i) f :=
  iSup_liminf_le_liminf_iSup (α := αᵒᵈ)

/--
theorem `limsup_eq_sInf_sSup` / 定理 `limsup_eq_sInf_sSup`

English:
theorem limsup_eq_sInf_sSup
  given: {ι R : Type*} (F : Filter ι) [CompleteLattice R] (a : ι -> R)
  proof: by
  apply le_antisymm
  · rw [limsup_eq]
    refine sInf_le_sInf fun x hx => ?_
    rcases (mem_image _ F.sets x).mp hx with ⟨I, ⟨I_mem_F, hI⟩⟩
    filter_upwards [I_mem_F] with i hi
    exact hI ▸ le_sSup (mem_image_of_mem _ hi)
· refine le_sInf fun b hb => sInf_le_of_le (mem_image_of_mem _ hb) sS

中文:
定理 limsup_eq_sInf_sSup
  条件: {ι R : 类型} (F : 滤子 ι) [完备格 R] (a : ι -> R)
  证明: by
  apply le_antisymm
  · rw [limsup_eq]
    refine sInf_le_sInf fun x hx => ?_
    rcases (mem_image _ F.sets x).mp hx with ⟨I, ⟨I_mem_F, hI⟩⟩
    filter_upwards [I_mem_F] with i hi
    exact hI ▸ le_sSup (mem_image_of_mem _ hi)
· refine le_sInf fun b hb => sInf_le_of_le (mem_image_of_mem _ hb) sS

Depends on / 依赖: F.sets, I_mem_F, filter_upwards, le_antisymm, le_sInf, le_sSup, limsup_eq, mem_image, mem_image_of_mem, sInf_le_of_le, sInf_le_sInf, sSup_le
-/
theorem limsup_eq_sInf_sSup {ι R : Type*} (F : Filter ι) [CompleteLattice R] (a : ι -> R) :
    limsup a F = sInf ((fun I => sSup (a '' I)) '' F.sets) := by
  apply le_antisymm
  · rw [limsup_eq]
    refine sInf_le_sInf fun x hx => ?_
    rcases (mem_image _ F.sets x).mp hx with ⟨I, ⟨I_mem_F, hI⟩⟩
    filter_upwards [I_mem_F] with i hi
    exact hI ▸ le_sSup (mem_image_of_mem _ hi)
· refine le_sInf fun b hb => sInf_le_of_le (mem_image_of_mem _ hb) sSup_le ?_
    rintro _ ⟨_, h, rfl⟩
    exact h

/--
theorem `liminf_eq_sSup_sInf` / 定理 `liminf_eq_sSup_sInf`

English:
theorem liminf_eq_sSup_sInf
  given: {ι R : Type*} (F : Filter ι) [CompleteLattice R] (a : ι -> R)
  proof: @Filter.limsup_eq_sInf_sSup ι (OrderDual R) _ _ a

中文:
定理 liminf_eq_sSup_sInf
  条件: {ι R : 类型} (F : 滤子 ι) [完备格 R] (a : ι -> R)
  证明: @Filter.limsup_eq_sInf_sSup ι (OrderDual R) _ _ a

Depends on / 依赖: Filter, Filter.limsup_eq_sInf_sSup, OrderDual, limsup_eq_sInf_sSup
-/
theorem liminf_eq_sSup_sInf {ι R : Type*} (F : Filter ι) [CompleteLattice R] (a : ι -> R) :
    liminf a F = sSup ((fun I => sInf (a '' I)) '' F.sets) :=
  @Filter.limsup_eq_sInf_sSup ι (OrderDual R) _ _ a

/--
theorem `liminf_le_of_frequently_le'` / 定理 `liminf_le_of_frequently_le'`

English:
theorem liminf_le_of_frequently_le'
  statement: {α β} [CompleteLattice β] {f : Filter α} {u : α -> β} {x : β}
  proof: by
  rw [liminf_eq]
  refine sSup_le fun b hb => ?_
  have hbx : existsᶠ _ in f, b <= x := by
    contrapose! h
    exact hb.mp (h.mono fun a hbx hba hax => hbx (hba.trans hax))
  exact hbx.exists.choose_spec

中文:
定理 liminf_le_of_frequently_le'
  结论: {α β} [完备格 β] {f : 滤子 α} {u : α -> β} {x : β}
  证明: by
  rw [liminf_eq]
  refine sSup_le fun b hb => ?_
  have hbx : existsᶠ _ in f, b <= x := by
    contrapose! h
    exact hb.mp (h.mono fun a hbx hba hax => hbx (hba.trans hax))
  exact hbx.exists.choose_spec

Depends on / 依赖: choose_spec, contrapose, h.mono, hb.mp, hba.trans, hbx.exists.choose_spec, liminf_eq, sSup_le
-/
theorem liminf_le_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α -> β} {x : β}
    (h : existsᶠ a in f, u a <= x) : liminf u f <= x := by
  rw [liminf_eq]
  refine sSup_le fun b hb => ?_
  have hbx : existsᶠ _ in f, b <= x := by
    contrapose! h
    exact hb.mp (h.mono fun a hbx hba hax => hbx (hba.trans hax))
  exact hbx.exists.choose_spec

/--
theorem `le_limsup_of_frequently_le'` / 定理 `le_limsup_of_frequently_le'`

English:
theorem le_limsup_of_frequently_le'
  statement: {α β} [CompleteLattice β] {f : Filter α} {u : α -> β} {x : β}
  proof: liminf_le_of_frequently_le' (β := βᵒᵈ) h

中文:
定理 le_limsup_of_frequently_le'
  结论: {α β} [完备格 β] {f : 滤子 α} {u : α -> β} {x : β}
  证明: liminf_le_of_frequently_le' (β := βᵒᵈ) h

Depends on / 依赖: liminf_le_of_frequently_le
-/
theorem le_limsup_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α -> β} {x : β}
    (h : existsᶠ a in f, x <= u a) : x <= limsup u f :=
  liminf_le_of_frequently_le' (β := βᵒᵈ) h

/-- If `f : α → α` is a morphism of complete lattices, then the limsup of its iterates of any
`a : α` is a fixed point. -/
@[simp]
/--
theorem `_root_.CompleteLatticeHom.apply_limsup_iterate` / 定理 `_root_.CompleteLatticeHom.apply_limsup_iterate`

English:
theorem _root_.CompleteLatticeHom.apply_limsup_iterate
  given: (f : CompleteLatticeHom α α) (a : α)
  proof: by
  rw [limsup_eq_iInf_iSup_of_nat']; rw [map_iInf]
  simp_rw [_root_.map_iSup, ← Function.comp_apply (f := f), ← Function.iterate_succ' f,
    ← Nat.add_succ]
  conv_rhs => rw [iInf_split _ (0 < ·)]
  simp only [not_lt, Nat.le_zero, iInf_iInf_eq_left, add_zero, iInf_nat_gt_zero_eq, left_eq_inf]
  

中文:
定理 _root_.完备格态射.apply_limsup_iterate
  条件: (f : 完备格态射 α α) (a : α)
  证明: by
  rw [limsup_eq_iInf_iSup_of_nat']; rw [map_iInf]
  simp_rw [_root_.map_iSup, ← Function.comp_apply (f := f), ← Function.iterate_succ' f,
    ← Nat.add_succ]
  conv_rhs => rw [iInf_split _ (0 < ·)]
  simp only [not_lt, Nat.le_zero, iInf_iInf_eq_left, add_zero, iInf_nat_gt_zero_eq, left_eq_inf]
  

Depends on / 依赖: Function, Function.comp_apply, Function.iterate_succ, Nat.add_succ, Nat.le_zero, _root_, _root_.map_iSup, add_succ, add_zero, comp_apply, conv_rhs, iInf_iInf_eq_left, iInf_le, iInf_nat_gt_zero_eq, iInf_split, iSup_le_iff, iterate_succ, le_iSup, le_zero, left_eq_inf
-/
theorem _root_.CompleteLatticeHom.apply_limsup_iterate (f : CompleteLatticeHom α α) (a : α) :
    f (limsup (fun n => f^[n] a) atTop) = limsup (fun n => f^[n] a) atTop := by
  rw [limsup_eq_iInf_iSup_of_nat']; rw [map_iInf]
  simp_rw [_root_.map_iSup, ← Function.comp_apply (f := f), ← Function.iterate_succ' f,
    ← Nat.add_succ]
  conv_rhs => rw [iInf_split _ (0 < ·)]
  simp only [not_lt, Nat.le_zero, iInf_iInf_eq_left, add_zero, iInf_nat_gt_zero_eq, left_eq_inf]
  refine (iInf_le (fun i => ⨆ j, f^[j + (i + 1)] a) 0).trans ?_
  simp only [zero_add, iSup_le_iff]
  exact fun i => le_iSup (fun i => f^[i] a) (i + 1)

/--
theorem `_root_.CompleteLatticeHom.apply_liminf_iterate` / 定理 `_root_.CompleteLatticeHom.apply_liminf_iterate`

English:
theorem _root_.CompleteLatticeHom.apply_liminf_iterate
  given: (f : CompleteLatticeHom α α) (a : α)
  proof: (CompleteLatticeHom.dual f).apply_limsup_iterate _

中文:
定理 _root_.完备格态射.apply_liminf_iterate
  条件: (f : 完备格态射 α α) (a : α)
  证明: (CompleteLatticeHom.dual f).apply_limsup_iterate _

Depends on / 依赖: CompleteLatticeHom, CompleteLatticeHom.dual, apply_limsup_iterate
-/
theorem _root_.CompleteLatticeHom.apply_liminf_iterate (f : CompleteLatticeHom α α) (a : α) :
    f (liminf (fun n => f^[n] a) atTop) = liminf (fun n => f^[n] a) atTop :=
  (CompleteLatticeHom.dual f).apply_limsup_iterate _

variable {f g : Filter β} {p q : β -> Prop} {u v : β -> α}

/--
theorem `blimsup_mono` / 定理 `blimsup_mono`

English:
theorem blimsup_mono
  given: (h : forall x, p x -> q x)
  statement: blimsup u f p <= blimsup u f q
  proof: sInf_le_sInf fun a ha => ha.mono by tauto

中文:
定理 blimsup_mono
  条件: (h : 对任意 x, p x -> q x)
  结论: blimsup u f p <= blimsup u f q
  证明: sInf_le_sInf fun a ha => ha.mono by tauto

Depends on / 依赖: ha.mono, sInf_le_sInf
-/
theorem blimsup_mono (h : forall x, p x -> q x) : blimsup u f p <= blimsup u f q :=
sInf_le_sInf fun a ha => ha.mono by tauto

/--
theorem `bliminf_antitone` / 定理 `bliminf_antitone`

English:
theorem bliminf_antitone
  given: (h : forall x, p x -> q x)
  statement: bliminf u f q <= bliminf u f p
  proof: sSup_le_sSup fun a ha => ha.mono by tauto

中文:
定理 bliminf_antitone
  条件: (h : 对任意 x, p x -> q x)
  结论: bliminf u f q <= bliminf u f p
  证明: sSup_le_sSup fun a ha => ha.mono by tauto

Depends on / 依赖: ha.mono, sSup_le_sSup
-/
theorem bliminf_antitone (h : forall x, p x -> q x) : bliminf u f q <= bliminf u f p :=
sSup_le_sSup fun a ha => ha.mono by tauto

/--
theorem `mono_blimsup'` / 定理 `mono_blimsup'`

English:
theorem mono_blimsup'
  given: (h : forallᶠ x in f, p x -> u x <= v x)
  statement: blimsup u f p <= blimsup v f p
  proof: sInf_le_sInf fun _ ha => (ha.and h).mono fun _ hx hx' => (hx.2 hx').trans (hx.1 hx')

中文:
定理 mono_blimsup'
  条件: (h : 对任意ᶠ x in f, p x -> u x <= v x)
  结论: blimsup u f p <= blimsup v f p
  证明: sInf_le_sInf fun _ ha => (ha.and h).mono fun _ hx hx' => (hx.2 hx').trans (hx.1 hx')

Depends on / 依赖: ha.and, sInf_le_sInf
-/
theorem mono_blimsup' (h : forallᶠ x in f, p x -> u x <= v x) : blimsup u f p <= blimsup v f p :=
  sInf_le_sInf fun _ ha => (ha.and h).mono fun _ hx hx' => (hx.2 hx').trans (hx.1 hx')

/--
theorem `mono_blimsup` / 定理 `mono_blimsup`

English:
theorem mono_blimsup
  given: (h : forall x, p x -> u x <= v x)
  statement: blimsup u f p <= blimsup v f p
  proof: mono_blimsup' Eventually.of_forall h

中文:
定理 mono_blimsup
  条件: (h : 对任意 x, p x -> u x <= v x)
  结论: blimsup u f p <= blimsup v f p
  证明: mono_blimsup' Eventually.of_forall h

Depends on / 依赖: Eventually, Eventually.of_forall, mono_blimsup, of_forall
-/
theorem mono_blimsup (h : forall x, p x -> u x <= v x) : blimsup u f p <= blimsup v f p :=
mono_blimsup' Eventually.of_forall h

/--
theorem `mono_bliminf'` / 定理 `mono_bliminf'`

English:
theorem mono_bliminf'
  given: (h : forallᶠ x in f, p x -> u x <= v x)
  statement: bliminf u f p <= bliminf v f p
  proof: sSup_le_sSup fun _ ha => (ha.and h).mono fun _ hx hx' => (hx.1 hx').trans (hx.2 hx')

中文:
定理 mono_bliminf'
  条件: (h : 对任意ᶠ x in f, p x -> u x <= v x)
  结论: bliminf u f p <= bliminf v f p
  证明: sSup_le_sSup fun _ ha => (ha.and h).mono fun _ hx hx' => (hx.1 hx').trans (hx.2 hx')

Depends on / 依赖: ha.and, sSup_le_sSup
-/
theorem mono_bliminf' (h : forallᶠ x in f, p x -> u x <= v x) : bliminf u f p <= bliminf v f p :=
  sSup_le_sSup fun _ ha => (ha.and h).mono fun _ hx hx' => (hx.1 hx').trans (hx.2 hx')

/--
theorem `mono_bliminf` / 定理 `mono_bliminf`

English:
theorem mono_bliminf
  given: (h : forall x, p x -> u x <= v x)
  statement: bliminf u f p <= bliminf v f p
  proof: mono_bliminf' Eventually.of_forall h

中文:
定理 mono_bliminf
  条件: (h : 对任意 x, p x -> u x <= v x)
  结论: bliminf u f p <= bliminf v f p
  证明: mono_bliminf' Eventually.of_forall h

Depends on / 依赖: Eventually, Eventually.of_forall, mono_bliminf, of_forall
-/
theorem mono_bliminf (h : forall x, p x -> u x <= v x) : bliminf u f p <= bliminf v f p :=
mono_bliminf' Eventually.of_forall h

/--
theorem `bliminf_antitone_filter` / 定理 `bliminf_antitone_filter`

English:
theorem bliminf_antitone_filter
  given: (h : f <= g)
  statement: bliminf u g p <= bliminf u f p
  proof: sSup_le_sSup fun _ ha => ha.filter_mono h

中文:
定理 bliminf_antitone_filter
  条件: (h : f <= g)
  结论: bliminf u g p <= bliminf u f p
  证明: sSup_le_sSup fun _ ha => ha.filter_mono h

Depends on / 依赖: filter_mono, ha.filter_mono, sSup_le_sSup
-/
theorem bliminf_antitone_filter (h : f <= g) : bliminf u g p <= bliminf u f p :=
  sSup_le_sSup fun _ ha => ha.filter_mono h

/--
theorem `blimsup_monotone_filter` / 定理 `blimsup_monotone_filter`

English:
theorem blimsup_monotone_filter
  given: (h : f <= g)
  statement: blimsup u f p <= blimsup u g p
  proof: sInf_le_sInf fun _ ha => ha.filter_mono h

中文:
定理 blimsup_monotone_filter
  条件: (h : f <= g)
  结论: blimsup u f p <= blimsup u g p
  证明: sInf_le_sInf fun _ ha => ha.filter_mono h

Depends on / 依赖: filter_mono, ha.filter_mono, sInf_le_sInf
-/
theorem blimsup_monotone_filter (h : f <= g) : blimsup u f p <= blimsup u g p :=
  sInf_le_sInf fun _ ha => ha.filter_mono h

/--
theorem `blimsup_and_le_inf` / 定理 `blimsup_and_le_inf`

English:
theorem blimsup_and_le_inf
  statement: (blimsup u f fun x => p x ∧ q x) <= blimsup u f p ⊓ blimsup u f q
  proof: le_inf (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)

@[simp]

中文:
定理 blimsup_and_le_inf
  结论: (blimsup u f fun x => p x ∧ q x) <= blimsup u f p ⊓ blimsup u f q
  证明: le_inf (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)

@[simp]

Depends on / 依赖: blimsup_mono, le_inf
-/
theorem blimsup_and_le_inf : (blimsup u f fun x => p x ∧ q x) <= blimsup u f p ⊓ blimsup u f q :=
  le_inf (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)

@[simp]
/--
theorem `bliminf_sup_le_inf_aux_left` / 定理 `bliminf_sup_le_inf_aux_left`

English:
theorem bliminf_sup_le_inf_aux_left
  proof: blimsup_and_le_inf.trans inf_le_left

@[simp]

中文:
定理 bliminf_sup_le_inf_aux_left
  证明: blimsup_and_le_inf.trans inf_le_left

@[simp]

Depends on / 依赖: blimsup_and_le_inf, blimsup_and_le_inf.trans, inf_le_left
-/
theorem bliminf_sup_le_inf_aux_left :
    (blimsup u f fun x => p x ∧ q x) <= blimsup u f p :=
  blimsup_and_le_inf.trans inf_le_left

@[simp]
/--
theorem `bliminf_sup_le_inf_aux_right` / 定理 `bliminf_sup_le_inf_aux_right`

English:
theorem bliminf_sup_le_inf_aux_right
  proof: blimsup_and_le_inf.trans inf_le_right

中文:
定理 bliminf_sup_le_inf_aux_right
  证明: blimsup_and_le_inf.trans inf_le_right

Depends on / 依赖: blimsup_and_le_inf, blimsup_and_le_inf.trans, inf_le_right
-/
theorem bliminf_sup_le_inf_aux_right :
    (blimsup u f fun x => p x ∧ q x) <= blimsup u f q :=
  blimsup_and_le_inf.trans inf_le_right

/--
theorem `bliminf_sup_le_and` / 定理 `bliminf_sup_le_and`

English:
theorem bliminf_sup_le_and
  statement: bliminf u f p ⊔ bliminf u f q <= bliminf u f fun x => p x ∧ q x
  proof: blimsup_and_le_inf (α := αᵒᵈ)

@[simp]

中文:
定理 bliminf_sup_le_and
  结论: bliminf u f p ⊔ bliminf u f q <= bliminf u f fun x => p x ∧ q x
  证明: blimsup_and_le_inf (α := αᵒᵈ)

@[simp]

Depends on / 依赖: blimsup_and_le_inf
-/
theorem bliminf_sup_le_and : bliminf u f p ⊔ bliminf u f q <= bliminf u f fun x => p x ∧ q x :=
  blimsup_and_le_inf (α := αᵒᵈ)

@[simp]
/--
theorem `bliminf_sup_le_and_aux_left` / 定理 `bliminf_sup_le_and_aux_left`

English:
theorem bliminf_sup_le_and_aux_left
  statement: bliminf u f p <= bliminf u f fun x => p x ∧ q x
  proof: le_sup_left.trans bliminf_sup_le_and

@[simp]

中文:
定理 bliminf_sup_le_and_aux_left
  结论: bliminf u f p <= bliminf u f fun x => p x ∧ q x
  证明: le_sup_left.trans bliminf_sup_le_and

@[simp]

Depends on / 依赖: bliminf_sup_le_and, le_sup_left, le_sup_left.trans
-/
theorem bliminf_sup_le_and_aux_left : bliminf u f p <= bliminf u f fun x => p x ∧ q x :=
  le_sup_left.trans bliminf_sup_le_and

@[simp]
/--
theorem `bliminf_sup_le_and_aux_right` / 定理 `bliminf_sup_le_and_aux_right`

English:
theorem bliminf_sup_le_and_aux_right
  statement: bliminf u f q <= bliminf u f fun x => p x ∧ q x
  proof: le_sup_right.trans bliminf_sup_le_and

中文:
定理 bliminf_sup_le_and_aux_right
  结论: bliminf u f q <= bliminf u f fun x => p x ∧ q x
  证明: le_sup_right.trans bliminf_sup_le_and

Depends on / 依赖: bliminf_sup_le_and, le_sup_right, le_sup_right.trans
-/
theorem bliminf_sup_le_and_aux_right : bliminf u f q <= bliminf u f fun x => p x ∧ q x :=
  le_sup_right.trans bliminf_sup_le_and

/--
theorem `blimsup_sup_le_or` / 定理 `blimsup_sup_le_or`

English:
theorem blimsup_sup_le_or
  statement: blimsup u f p ⊔ blimsup u f q <= blimsup u f fun x => p x ∨ q x
  proof: sup_le (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)

@[simp]

中文:
定理 blimsup_sup_le_or
  结论: blimsup u f p ⊔ blimsup u f q <= blimsup u f fun x => p x ∨ q x
  证明: sup_le (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)

@[simp]

Depends on / 依赖: blimsup_mono, sup_le
-/
theorem blimsup_sup_le_or : blimsup u f p ⊔ blimsup u f q <= blimsup u f fun x => p x ∨ q x :=
  sup_le (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)

@[simp]
/--
theorem `bliminf_sup_le_or_aux_left` / 定理 `bliminf_sup_le_or_aux_left`

English:
theorem bliminf_sup_le_or_aux_left
  statement: blimsup u f p <= blimsup u f fun x => p x ∨ q x
  proof: le_sup_left.trans blimsup_sup_le_or

@[simp]

中文:
定理 bliminf_sup_le_or_aux_left
  结论: blimsup u f p <= blimsup u f fun x => p x ∨ q x
  证明: le_sup_left.trans blimsup_sup_le_or

@[simp]

Depends on / 依赖: blimsup_sup_le_or, le_sup_left, le_sup_left.trans
-/
theorem bliminf_sup_le_or_aux_left : blimsup u f p <= blimsup u f fun x => p x ∨ q x :=
  le_sup_left.trans blimsup_sup_le_or

@[simp]
/--
theorem `bliminf_sup_le_or_aux_right` / 定理 `bliminf_sup_le_or_aux_right`

English:
theorem bliminf_sup_le_or_aux_right
  statement: blimsup u f q <= blimsup u f fun x => p x ∨ q x
  proof: le_sup_right.trans blimsup_sup_le_or

中文:
定理 bliminf_sup_le_or_aux_right
  结论: blimsup u f q <= blimsup u f fun x => p x ∨ q x
  证明: le_sup_right.trans blimsup_sup_le_or

Depends on / 依赖: blimsup_sup_le_or, le_sup_right, le_sup_right.trans
-/
theorem bliminf_sup_le_or_aux_right : blimsup u f q <= blimsup u f fun x => p x ∨ q x :=
  le_sup_right.trans blimsup_sup_le_or

/--
theorem `bliminf_or_le_inf` / 定理 `bliminf_or_le_inf`

English:
theorem bliminf_or_le_inf
  statement: (bliminf u f fun x => p x ∨ q x) <= bliminf u f p ⊓ bliminf u f q
  proof: blimsup_sup_le_or (α := αᵒᵈ)

@[simp]

中文:
定理 bliminf_or_le_inf
  结论: (bliminf u f fun x => p x ∨ q x) <= bliminf u f p ⊓ bliminf u f q
  证明: blimsup_sup_le_or (α := αᵒᵈ)

@[simp]

Depends on / 依赖: blimsup_sup_le_or
-/
theorem bliminf_or_le_inf : (bliminf u f fun x => p x ∨ q x) <= bliminf u f p ⊓ bliminf u f q :=
  blimsup_sup_le_or (α := αᵒᵈ)

@[simp]
/--
theorem `bliminf_or_le_inf_aux_left` / 定理 `bliminf_or_le_inf_aux_left`

English:
theorem bliminf_or_le_inf_aux_left
  statement: (bliminf u f fun x => p x ∨ q x) <= bliminf u f p
  proof: bliminf_or_le_inf.trans inf_le_left

@[simp]

中文:
定理 bliminf_or_le_inf_aux_left
  结论: (bliminf u f fun x => p x ∨ q x) <= bliminf u f p
  证明: bliminf_or_le_inf.trans inf_le_left

@[simp]

Depends on / 依赖: bliminf_or_le_inf, bliminf_or_le_inf.trans, inf_le_left
-/
theorem bliminf_or_le_inf_aux_left : (bliminf u f fun x => p x ∨ q x) <= bliminf u f p :=
  bliminf_or_le_inf.trans inf_le_left

@[simp]
/--
theorem `bliminf_or_le_inf_aux_right` / 定理 `bliminf_or_le_inf_aux_right`

English:
theorem bliminf_or_le_inf_aux_right
  statement: (bliminf u f fun x => p x ∨ q x) <= bliminf u f q
  proof: bliminf_or_le_inf.trans inf_le_right

中文:
定理 bliminf_or_le_inf_aux_right
  结论: (bliminf u f fun x => p x ∨ q x) <= bliminf u f q
  证明: bliminf_or_le_inf.trans inf_le_right

Depends on / 依赖: bliminf_or_le_inf, bliminf_or_le_inf.trans, inf_le_right
-/
theorem bliminf_or_le_inf_aux_right : (bliminf u f fun x => p x ∨ q x) <= bliminf u f q :=
  bliminf_or_le_inf.trans inf_le_right

/--
theorem `_root_.OrderIso.apply_blimsup` / 定理 `_root_.OrderIso.apply_blimsup`

English:
theorem _root_.OrderIso.apply_blimsup
  given: [CompleteLattice γ] (e : α ≃o γ)
  proof: by
  simp only [blimsup_eq, map_sInf, Function.comp_apply, e.image_eq_preimage_symm,
    Set.preimage_ofPred_eq, e.le_symm_apply]

中文:
定理 _root_.OrderIso.apply_blimsup
  条件: [完备格 γ] (e : α ≃o γ)
  证明: by
  simp only [blimsup_eq, map_sInf, Function.comp_apply, e.image_eq_preimage_symm,
    Set.preimage_ofPred_eq, e.le_symm_apply]

Depends on / 依赖: Function, Function.comp_apply, Set.preimage_ofPred_eq, blimsup_eq, comp_apply, e.image_eq_preimage_symm, e.le_symm_apply, image_eq_preimage_symm, le_symm_apply, map_sInf, preimage_ofPred_eq
-/
theorem _root_.OrderIso.apply_blimsup [CompleteLattice γ] (e : α ≃o γ) :
    e (blimsup u f p) = blimsup (e ∘ u) f p := by
  simp only [blimsup_eq, map_sInf, Function.comp_apply, e.image_eq_preimage_symm,
    Set.preimage_ofPred_eq, e.le_symm_apply]

/--
theorem `_root_.OrderIso.apply_bliminf` / 定理 `_root_.OrderIso.apply_bliminf`

English:
theorem _root_.OrderIso.apply_bliminf
  given: [CompleteLattice γ] (e : α ≃o γ)
  proof: e.dual.apply_blimsup

中文:
定理 _root_.OrderIso.apply_bliminf
  条件: [完备格 γ] (e : α ≃o γ)
  证明: e.dual.apply_blimsup

Depends on / 依赖: apply_blimsup, e.dual.apply_blimsup
-/
theorem _root_.OrderIso.apply_bliminf [CompleteLattice γ] (e : α ≃o γ) :
    e (bliminf u f p) = bliminf (e ∘ u) f p :=
  e.dual.apply_blimsup

/--
theorem `_root_.sSupHom.apply_blimsup_le` / 定理 `_root_.sSupHom.apply_blimsup_le`

English:
theorem _root_.sSupHom.apply_blimsup_le
  given: [CompleteLattice γ] (g : sSupHom α γ)
  proof: by
  simp only [blimsup_eq_iInf_biSup, Function.comp]
  refine ((OrderHomClass.mono g).map_iInf₂_le _).trans ?_
  simp only [_root_.map_iSup, le_refl]

中文:
定理 _root_.sSup态射.apply_blimsup_le
  条件: [完备格 γ] (g : sSup态射 α γ)
  证明: by
  simp only [blimsup_eq_iInf_biSup, Function.comp]
  refine ((OrderHomClass.mono g).map_iInf₂_le _).trans ?_
  simp only [_root_.map_iSup, le_refl]

Depends on / 依赖: Function, Function.comp, OrderHomClass, OrderHomClass.mono, _root_, _root_.map_iSup, blimsup_eq_iInf_biSup, le_refl, map_iSup
-/
theorem _root_.sSupHom.apply_blimsup_le [CompleteLattice γ] (g : sSupHom α γ) :
    g (blimsup u f p) <= blimsup (g ∘ u) f p := by
  simp only [blimsup_eq_iInf_biSup, Function.comp]
  refine ((OrderHomClass.mono g).map_iInf₂_le _).trans ?_
  simp only [_root_.map_iSup, le_refl]

/--
theorem `_root_.sInfHom.le_apply_bliminf` / 定理 `_root_.sInfHom.le_apply_bliminf`

English:
theorem _root_.sInfHom.le_apply_bliminf
  given: [CompleteLattice γ] (g : sInfHom α γ)
  proof: (sInfHom.dual g).apply_blimsup_le

中文:
定理 _root_.sInf态射.le_apply_bliminf
  条件: [完备格 γ] (g : sInf态射 α γ)
  证明: (sInfHom.dual g).apply_blimsup_le

Depends on / 依赖: apply_blimsup_le, sInfHom, sInfHom.dual
-/
theorem _root_.sInfHom.le_apply_bliminf [CompleteLattice γ] (g : sInfHom α γ) :
    bliminf (g ∘ u) f p <= g (bliminf u f p) :=
  (sInfHom.dual g).apply_blimsup_le

end CompleteLattice

section CompleteDistribLattice

variable [CompleteDistribLattice α] {f : Filter β} {p q : β -> Prop} {u : β -> α}

/--
lemma `limsup_sup_filter` / 引理 `limsup_sup_filter`

English:
lemma limsup_sup_filter
  given: {g}
  statement: limsup u (f ⊔ g) = limsup u f ⊔ limsup u g
  proof: by
  refine le_antisymm ?_
    (sup_le (limsup_le_limsup_of_le le_sup_left) (limsup_le_limsup_of_le le_sup_right))
  simp_rw [limsup_eq, sInf_sup_eq, sup_sInf_eq, mem_ofPred_eq, le_iInf₂_iff]
  intro a ha b hb
  exact sInf_le ⟨ha.mono fun _ h => h.trans le_sup_left, hb.mono fun _ h => h.trans le_sup

中文:
引理 limsup_sup_filter
  条件: {g}
  结论: limsup u (f ⊔ g) = limsup u f ⊔ limsup u g
  证明: by
  refine le_antisymm ?_
    (sup_le (limsup_le_limsup_of_le le_sup_left) (limsup_le_limsup_of_le le_sup_right))
  simp_rw [limsup_eq, sInf_sup_eq, sup_sInf_eq, mem_ofPred_eq, le_iInf₂_iff]
  intro a ha b hb
  exact sInf_le ⟨ha.mono fun _ h => h.trans le_sup_left, hb.mono fun _ h => h.trans le_sup

Depends on / 依赖: h.trans, ha.mono, hb.mono, le_antisymm, le_sup_left, le_sup_right, limsup_eq, limsup_le_limsup_of_le, mem_ofPred_eq, sInf_le, sInf_sup_eq, simp_rw, sup_le, sup_sInf_eq
-/
lemma limsup_sup_filter {g} : limsup u (f ⊔ g) = limsup u f ⊔ limsup u g := by
  refine le_antisymm ?_
    (sup_le (limsup_le_limsup_of_le le_sup_left) (limsup_le_limsup_of_le le_sup_right))
  simp_rw [limsup_eq, sInf_sup_eq, sup_sInf_eq, mem_ofPred_eq, le_iInf₂_iff]
  intro a ha b hb
  exact sInf_le ⟨ha.mono fun _ h => h.trans le_sup_left, hb.mono fun _ h => h.trans le_sup_right⟩

/--
lemma `liminf_sup_filter` / 引理 `liminf_sup_filter`

English:
lemma liminf_sup_filter
  given: {g}
  statement: liminf u (f ⊔ g) = liminf u f ⊓ liminf u g
  proof: limsup_sup_filter (α := αᵒᵈ)

@[simp]

中文:
引理 liminf_sup_filter
  条件: {g}
  结论: liminf u (f ⊔ g) = liminf u f ⊓ liminf u g
  证明: limsup_sup_filter (α := αᵒᵈ)

@[simp]

Depends on / 依赖: limsup_sup_filter
-/
lemma liminf_sup_filter {g} : liminf u (f ⊔ g) = liminf u f ⊓ liminf u g :=
  limsup_sup_filter (α := αᵒᵈ)

@[simp]
/--
theorem `blimsup_or_eq_sup` / 定理 `blimsup_or_eq_sup`

English:
theorem blimsup_or_eq_sup
  statement: (blimsup u f fun x => p x ∨ q x) = blimsup u f p ⊔ blimsup u f q
  proof: by
  simp only [blimsup_eq_limsup, ← limsup_sup_filter, ← inf_sup_left, sup_principal, ofPred_or]

@[simp]

中文:
定理 blimsup_or_eq_sup
  结论: (blimsup u f fun x => p x ∨ q x) = blimsup u f p ⊔ blimsup u f q
  证明: by
  simp only [blimsup_eq_limsup, ← limsup_sup_filter, ← inf_sup_left, sup_principal, ofPred_or]

@[simp]

Depends on / 依赖: blimsup_eq_limsup, inf_sup_left, limsup_sup_filter, ofPred_or, sup_principal
-/
theorem blimsup_or_eq_sup : (blimsup u f fun x => p x ∨ q x) = blimsup u f p ⊔ blimsup u f q := by
  simp only [blimsup_eq_limsup, ← limsup_sup_filter, ← inf_sup_left, sup_principal, ofPred_or]

@[simp]
/--
theorem `bliminf_or_eq_inf` / 定理 `bliminf_or_eq_inf`

English:
theorem bliminf_or_eq_inf
  statement: (bliminf u f fun x => p x ∨ q x) = bliminf u f p ⊓ bliminf u f q
  proof: blimsup_or_eq_sup (α := αᵒᵈ)

@[simp]

中文:
定理 bliminf_or_eq_inf
  结论: (bliminf u f fun x => p x ∨ q x) = bliminf u f p ⊓ bliminf u f q
  证明: blimsup_or_eq_sup (α := αᵒᵈ)

@[simp]

Depends on / 依赖: blimsup_or_eq_sup
-/
theorem bliminf_or_eq_inf : (bliminf u f fun x => p x ∨ q x) = bliminf u f p ⊓ bliminf u f q :=
  blimsup_or_eq_sup (α := αᵒᵈ)

@[simp]
/--
lemma `blimsup_sup_not` / 引理 `blimsup_sup_not`

English:
lemma blimsup_sup_not
  statement: blimsup u f p ⊔ blimsup u f (¬p ·) = limsup u f
  proof: by
  simp_rw [← blimsup_or_eq_sup, or_not, blimsup_true]

@[simp]

中文:
引理 blimsup_sup_not
  结论: blimsup u f p ⊔ blimsup u f (¬p ·) = limsup u f
  证明: by
  simp_rw [← blimsup_or_eq_sup, or_not, blimsup_true]

@[simp]

Depends on / 依赖: blimsup_or_eq_sup, blimsup_true, or_not, simp_rw
-/
lemma blimsup_sup_not : blimsup u f p ⊔ blimsup u f (¬p ·) = limsup u f := by
  simp_rw [← blimsup_or_eq_sup, or_not, blimsup_true]

@[simp]
/--
lemma `bliminf_inf_not` / 引理 `bliminf_inf_not`

English:
lemma bliminf_inf_not
  statement: bliminf u f p ⊓ bliminf u f (¬p ·) = liminf u f
  proof: blimsup_sup_not (α := αᵒᵈ)

@[simp]

中文:
引理 bliminf_inf_not
  结论: bliminf u f p ⊓ bliminf u f (¬p ·) = liminf u f
  证明: blimsup_sup_not (α := αᵒᵈ)

@[simp]

Depends on / 依赖: blimsup_sup_not
-/
lemma bliminf_inf_not : bliminf u f p ⊓ bliminf u f (¬p ·) = liminf u f :=
  blimsup_sup_not (α := αᵒᵈ)

@[simp]
/--
lemma `blimsup_not_sup` / 引理 `blimsup_not_sup`

English:
lemma blimsup_not_sup
  statement: blimsup u f (¬p ·) ⊔ blimsup u f p = limsup u f
  proof: by
  simpa only [not_not] using blimsup_sup_not (p := (¬p ·))

@[simp]

中文:
引理 blimsup_not_sup
  结论: blimsup u f (¬p ·) ⊔ blimsup u f p = limsup u f
  证明: by
  simpa only [not_not] using blimsup_sup_not (p := (¬p ·))

@[simp]

Depends on / 依赖: blimsup_sup_not, not_not
-/
lemma blimsup_not_sup : blimsup u f (¬p ·) ⊔ blimsup u f p = limsup u f := by
  simpa only [not_not] using blimsup_sup_not (p := (¬p ·))

@[simp]
/--
lemma `bliminf_not_inf` / 引理 `bliminf_not_inf`

English:
lemma bliminf_not_inf
  statement: bliminf u f (¬p ·) ⊓ bliminf u f p = liminf u f
  proof: blimsup_not_sup (α := αᵒᵈ)

中文:
引理 bliminf_not_inf
  结论: bliminf u f (¬p ·) ⊓ bliminf u f p = liminf u f
  证明: blimsup_not_sup (α := αᵒᵈ)

Depends on / 依赖: blimsup_not_sup
-/
lemma bliminf_not_inf : bliminf u f (¬p ·) ⊓ bliminf u f p = liminf u f :=
  blimsup_not_sup (α := αᵒᵈ)

/--
lemma `limsup_piecewise` / 引理 `limsup_piecewise`

English:
lemma limsup_piecewise
  given: {s : Set β} [DecidablePred (· in s)] {v}
  proof: by
  rw [← blimsup_sup_not (p := (· in s))]
  refine congr_arg₂ _ (blimsup_congr ?_) (blimsup_congr ?_) <;>
    filter_upwards with _ h using by simp [h]

中文:
引理 limsup_piecewise
  条件: {s : 集合 β} [DecidablePred (· in s)] {v}
  证明: by
  rw [← blimsup_sup_not (p := (· in s))]
  refine congr_arg₂ _ (blimsup_congr ?_) (blimsup_congr ?_) <;>
    filter_upwards with _ h using by simp [h]

Depends on / 依赖: blimsup_congr, blimsup_sup_not, filter_upwards
-/
lemma limsup_piecewise {s : Set β} [DecidablePred (· in s)] {v} :
    limsup (s.piecewise u v) f = blimsup u f (· in s) ⊔ blimsup v f (· ∉ s) := by
  rw [← blimsup_sup_not (p := (· in s))]
  refine congr_arg₂ _ (blimsup_congr ?_) (blimsup_congr ?_) <;>
    filter_upwards with _ h using by simp [h]

/--
lemma `liminf_piecewise` / 引理 `liminf_piecewise`

English:
lemma liminf_piecewise
  given: {s : Set β} [DecidablePred (· in s)] {v}
  proof: limsup_piecewise (α := αᵒᵈ)

中文:
引理 liminf_piecewise
  条件: {s : 集合 β} [DecidablePred (· in s)] {v}
  证明: limsup_piecewise (α := αᵒᵈ)

Depends on / 依赖: limsup_piecewise
-/
lemma liminf_piecewise {s : Set β} [DecidablePred (· in s)] {v} :
    liminf (s.piecewise u v) f = bliminf u f (· in s) ⊓ bliminf v f (· ∉ s) :=
  limsup_piecewise (α := αᵒᵈ)

/--
theorem `sup_limsup` / 定理 `sup_limsup`

English:
theorem sup_limsup
  given: [NeBot f] (a : α)
  statement: a ⊔ limsup u f = limsup (fun x => a ⊔ u x) f
  proof: by
  simp only [limsup_eq_iInf_iSup, iSup_sup_eq, sup_iInf₂_eq]
  congr; ext s; congr; ext hs; congr
  exact (biSup_const (nonempty_of_mem hs)).symm

中文:
定理 sup_limsup
  条件: [NeBot f] (a : α)
  结论: a ⊔ limsup u f = limsup (fun x => a ⊔ u x) f
  证明: by
  simp only [limsup_eq_iInf_iSup, iSup_sup_eq, sup_iInf₂_eq]
  congr; ext s; congr; ext hs; congr
  exact (biSup_const (nonempty_of_mem hs)).symm

Depends on / 依赖: biSup_const, iSup_sup_eq, limsup_eq_iInf_iSup, nonempty_of_mem
-/
theorem sup_limsup [NeBot f] (a : α) : a ⊔ limsup u f = limsup (fun x => a ⊔ u x) f := by
  simp only [limsup_eq_iInf_iSup, iSup_sup_eq, sup_iInf₂_eq]
  congr; ext s; congr; ext hs; congr
  exact (biSup_const (nonempty_of_mem hs)).symm

/--
theorem `inf_liminf` / 定理 `inf_liminf`

English:
theorem inf_liminf
  given: [NeBot f] (a : α)
  statement: a ⊓ liminf u f = liminf (fun x => a ⊓ u x) f
  proof: sup_limsup (α := αᵒᵈ) a

中文:
定理 inf_liminf
  条件: [NeBot f] (a : α)
  结论: a ⊓ liminf u f = liminf (fun x => a ⊓ u x) f
  证明: sup_limsup (α := αᵒᵈ) a

Depends on / 依赖: sup_limsup
-/
theorem inf_liminf [NeBot f] (a : α) : a ⊓ liminf u f = liminf (fun x => a ⊓ u x) f :=
  sup_limsup (α := αᵒᵈ) a

/--
theorem `sup_liminf` / 定理 `sup_liminf`

English:
theorem sup_liminf
  given: (a : α)
  statement: a ⊔ liminf u f = liminf (fun x => a ⊔ u x) f
  proof: by
  simp only [liminf_eq_iSup_iInf]
  rw [sup_comm]; rw [biSup_sup (⟨univ]; rw [univ_mem⟩ : exists i : Set β]; rw [i in f)]
  simp_rw [iInf₂_sup_eq, sup_comm (a := a)]

中文:
定理 sup_liminf
  条件: (a : α)
  结论: a ⊔ liminf u f = liminf (fun x => a ⊔ u x) f
  证明: by
  simp only [liminf_eq_iSup_iInf]
  rw [sup_comm]; rw [biSup_sup (⟨univ]; rw [univ_mem⟩ : exists i : Set β]; rw [i in f)]
  simp_rw [iInf₂_sup_eq, sup_comm (a := a)]

Depends on / 依赖: biSup_sup, liminf_eq_iSup_iInf, simp_rw, sup_comm, univ_mem
-/
theorem sup_liminf (a : α) : a ⊔ liminf u f = liminf (fun x => a ⊔ u x) f := by
  simp only [liminf_eq_iSup_iInf]
  rw [sup_comm]; rw [biSup_sup (⟨univ]; rw [univ_mem⟩ : exists i : Set β]; rw [i in f)]
  simp_rw [iInf₂_sup_eq, sup_comm (a := a)]

/--
theorem `inf_limsup` / 定理 `inf_limsup`

English:
theorem inf_limsup
  given: (a : α)
  statement: a ⊓ limsup u f = limsup (fun x => a ⊓ u x) f
  proof: sup_liminf (α := αᵒᵈ) a

中文:
定理 inf_limsup
  条件: (a : α)
  结论: a ⊓ limsup u f = limsup (fun x => a ⊓ u x) f
  证明: sup_liminf (α := αᵒᵈ) a

Depends on / 依赖: sup_liminf
-/
theorem inf_limsup (a : α) : a ⊓ limsup u f = limsup (fun x => a ⊓ u x) f :=
  sup_liminf (α := αᵒᵈ) a

end CompleteDistribLattice

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] (f : Filter β) (u : β -> α)

/--
theorem `limsup_compl` / 定理 `limsup_compl`

English:
theorem limsup_compl
  statement: (limsup u f)ᶜ = liminf (compl ∘ u) f
  proof: by
  simp only [limsup_eq_iInf_iSup, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, Function.comp_apply]

中文:
定理 limsup_compl
  结论: (limsup u f)ᶜ = liminf (compl ∘ u) f
  证明: by
  simp only [limsup_eq_iInf_iSup, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, limsup_eq_iInf_iSup
-/
theorem limsup_compl : (limsup u f)ᶜ = liminf (compl ∘ u) f := by
  simp only [limsup_eq_iInf_iSup, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, Function.comp_apply]

/--
theorem `liminf_compl` / 定理 `liminf_compl`

English:
theorem liminf_compl
  statement: (liminf u f)ᶜ = limsup (compl ∘ u) f
  proof: by
  simp only [limsup_eq_iInf_iSup, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, Function.comp_apply]

中文:
定理 liminf_compl
  结论: (liminf u f)ᶜ = limsup (compl ∘ u) f
  证明: by
  simp only [limsup_eq_iInf_iSup, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, limsup_eq_iInf_iSup
-/
theorem liminf_compl : (liminf u f)ᶜ = limsup (compl ∘ u) f := by
  simp only [limsup_eq_iInf_iSup, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, Function.comp_apply]

/--
theorem `limsup_sdiff` / 定理 `limsup_sdiff`

English:
theorem limsup_sdiff
  given: (a : α)
  statement: limsup u f \ a = limsup (fun b => u b \ a) f
  proof: by
  simp only [limsup_eq_iInf_iSup, _root_.sdiff_eq]
  rw [biInf_inf (⟨univ]; rw [univ_mem⟩ : exists i : Set β]; rw [i in f)]
  simp_rw [inf_comm, inf_iSup₂_eq, inf_comm]

中文:
定理 limsup_sdiff
  条件: (a : α)
  结论: limsup u f \ a = limsup (fun b => u b \ a) f
  证明: by
  simp only [limsup_eq_iInf_iSup, _root_.sdiff_eq]
  rw [biInf_inf (⟨univ]; rw [univ_mem⟩ : exists i : Set β]; rw [i in f)]
  simp_rw [inf_comm, inf_iSup₂_eq, inf_comm]

Depends on / 依赖: _root_, _root_.sdiff_eq, biInf_inf, inf_comm, limsup_eq_iInf_iSup, sdiff_eq, simp_rw, univ_mem
-/
theorem limsup_sdiff (a : α) : limsup u f \ a = limsup (fun b => u b \ a) f := by
  simp only [limsup_eq_iInf_iSup, _root_.sdiff_eq]
  rw [biInf_inf (⟨univ]; rw [univ_mem⟩ : exists i : Set β]; rw [i in f)]
  simp_rw [inf_comm, inf_iSup₂_eq, inf_comm]

/--
theorem `liminf_sdiff` / 定理 `liminf_sdiff`

English:
theorem liminf_sdiff
  given: [NeBot f] (a : α)
  statement: liminf u f \ a = liminf (fun b => u b \ a) f
  proof: by
  simp only [_root_.sdiff_eq, inf_comm _ aᶜ, inf_liminf]

中文:
定理 liminf_sdiff
  条件: [NeBot f] (a : α)
  结论: liminf u f \ a = liminf (fun b => u b \ a) f
  证明: by
  simp only [_root_.sdiff_eq, inf_comm _ aᶜ, inf_liminf]

Depends on / 依赖: _root_, _root_.sdiff_eq, inf_comm, inf_liminf, sdiff_eq
-/
theorem liminf_sdiff [NeBot f] (a : α) : liminf u f \ a = liminf (fun b => u b \ a) f := by
  simp only [_root_.sdiff_eq, inf_comm _ aᶜ, inf_liminf]

/--
theorem `sdiff_limsup` / 定理 `sdiff_limsup`

English:
theorem sdiff_limsup
  given: [NeBot f] (a : α)
  statement: a \ limsup u f = liminf (fun b => a \ u b) f
  proof: by
  rw [← compl_inj_iff]
  simp only [_root_.sdiff_eq, liminf_compl, comp_def, compl_inf, compl_compl, sup_limsup]

中文:
定理 sdiff_limsup
  条件: [NeBot f] (a : α)
  结论: a \ limsup u f = liminf (fun b => a \ u b) f
  证明: by
  rw [← compl_inj_iff]
  simp only [_root_.sdiff_eq, liminf_compl, comp_def, compl_inf, compl_compl, sup_limsup]

Depends on / 依赖: _root_, _root_.sdiff_eq, comp_def, compl_compl, compl_inf, compl_inj_iff, liminf_compl, sdiff_eq, sup_limsup
-/
theorem sdiff_limsup [NeBot f] (a : α) : a \ limsup u f = liminf (fun b => a \ u b) f := by
  rw [← compl_inj_iff]
  simp only [_root_.sdiff_eq, liminf_compl, comp_def, compl_inf, compl_compl, sup_limsup]

/--
theorem `sdiff_liminf` / 定理 `sdiff_liminf`

English:
theorem sdiff_liminf
  given: (a : α)
  statement: a \ liminf u f = limsup (fun b => a \ u b) f
  proof: by
  rw [← compl_inj_iff]
  simp only [_root_.sdiff_eq, limsup_compl, comp_def, compl_inf, compl_compl, sup_liminf]

中文:
定理 sdiff_liminf
  条件: (a : α)
  结论: a \ liminf u f = limsup (fun b => a \ u b) f
  证明: by
  rw [← compl_inj_iff]
  simp only [_root_.sdiff_eq, limsup_compl, comp_def, compl_inf, compl_compl, sup_liminf]

Depends on / 依赖: _root_, _root_.sdiff_eq, comp_def, compl_compl, compl_inf, compl_inj_iff, limsup_compl, sdiff_eq, sup_liminf
-/
theorem sdiff_liminf (a : α) : a \ liminf u f = limsup (fun b => a \ u b) f := by
  rw [← compl_inj_iff]
  simp only [_root_.sdiff_eq, limsup_compl, comp_def, compl_inf, compl_compl, sup_liminf]

end CompleteBooleanAlgebra

section SetLattice

variable {p : ι -> Prop} {s : ι -> Set α} {𝓕 : Filter ι} {a : α}

/--
lemma `mem_liminf_iff_eventually_mem` / 引理 `mem_liminf_iff_eventually_mem`

English:
lemma mem_liminf_iff_eventually_mem
  statement: (a in liminf s 𝓕) ↔ (forallᶠ i in 𝓕, a in s i)
  proof: by
  simpa only [liminf_eq_iSup_iInf, iSup_eq_iUnion, iInf_eq_iInter, mem_iUnion, mem_iInter]
    using ⟨fun ⟨S, hS, hS'⟩ => mem_of_superset hS (by tauto), fun h => ⟨{i | a in s i}, h, by tauto⟩⟩

中文:
引理 mem_liminf_iff_eventually_mem
  结论: (a in liminf s 𝓕) ↔ (对任意ᶠ i in 𝓕, a in s i)
  证明: by
  simpa only [liminf_eq_iSup_iInf, iSup_eq_iUnion, iInf_eq_iInter, mem_iUnion, mem_iInter]
    using ⟨fun ⟨S, hS, hS'⟩ => mem_of_superset hS (by tauto), fun h => ⟨{i | a in s i}, h, by tauto⟩⟩

Depends on / 依赖: iInf_eq_iInter, iSup_eq_iUnion, liminf_eq_iSup_iInf, mem_iInter, mem_iUnion, mem_of_superset
-/
lemma mem_liminf_iff_eventually_mem : (a in liminf s 𝓕) ↔ (forallᶠ i in 𝓕, a in s i) := by
  simpa only [liminf_eq_iSup_iInf, iSup_eq_iUnion, iInf_eq_iInter, mem_iUnion, mem_iInter]
    using ⟨fun ⟨S, hS, hS'⟩ => mem_of_superset hS (by tauto), fun h => ⟨{i | a in s i}, h, by tauto⟩⟩

/--
lemma `mem_limsup_iff_frequently_mem` / 引理 `mem_limsup_iff_frequently_mem`

English:
lemma mem_limsup_iff_frequently_mem
  statement: (a in limsup s 𝓕) ↔ (existsᶠ i in 𝓕, a in s i)
  proof: by
  simp only [Filter.Frequently, iff_not_comm, ← mem_compl_iff, limsup_compl, comp_apply,
    mem_liminf_iff_eventually_mem]

中文:
引理 mem_limsup_iff_frequently_mem
  结论: (a in limsup s 𝓕) ↔ (存在ᶠ i in 𝓕, a in s i)
  证明: by
  simp only [Filter.Frequently, iff_not_comm, ← mem_compl_iff, limsup_compl, comp_apply,
    mem_liminf_iff_eventually_mem]

Depends on / 依赖: Filter, Filter.Frequently, Frequently, comp_apply, iff_not_comm, limsup_compl, mem_compl_iff, mem_liminf_iff_eventually_mem
-/
lemma mem_limsup_iff_frequently_mem : (a in limsup s 𝓕) ↔ (existsᶠ i in 𝓕, a in s i) := by
  simp only [Filter.Frequently, iff_not_comm, ← mem_compl_iff, limsup_compl, comp_apply,
    mem_liminf_iff_eventually_mem]

/--
theorem `cofinite.blimsup_set_eq` / 定理 `cofinite.blimsup_set_eq`

English:
theorem cofinite.blimsup_set_eq
  proof: by
  simp only [blimsup_eq, eventually_cofinite, not_forall, sInf_eq_sInter, exists_prop]
  ext x
  refine ⟨fun h => ?_, fun hx t h => ?_⟩ <;> contrapose h
  · simp only [mem_sInter, mem_ofPred_eq, not_forall, exists_prop]
    exact ⟨{x}ᶜ, by simpa using h, by simp⟩
  · exact hx.mono fun i hi => ⟨hi

中文:
定理 cofinite.blimsup_set_eq
  证明: by
  simp only [blimsup_eq, eventually_cofinite, not_forall, sInf_eq_sInter, exists_prop]
  ext x
  refine ⟨fun h => ?_, fun hx t h => ?_⟩ <;> contrapose h
  · simp only [mem_sInter, mem_ofPred_eq, not_forall, exists_prop]
    exact ⟨{x}ᶜ, by simpa using h, by simp⟩
  · exact hx.mono fun i hi => ⟨hi

Depends on / 依赖: blimsup_eq, contrapose, eventually_cofinite, exists_prop, hx.mono, mem_ofPred_eq, mem_sInter, not_forall, sInf_eq_sInter
-/
theorem cofinite.blimsup_set_eq :
    blimsup s cofinite p = { x | { n | p n ∧ x in s n }.Infinite } := by
  simp only [blimsup_eq, eventually_cofinite, not_forall, sInf_eq_sInter, exists_prop]
  ext x
  refine ⟨fun h => ?_, fun hx t h => ?_⟩ <;> contrapose h
  · simp only [mem_sInter, mem_ofPred_eq, not_forall, exists_prop]
    exact ⟨{x}ᶜ, by simpa using h, by simp⟩
  · exact hx.mono fun i hi => ⟨hi.1, fun hit => h (hit hi.2)⟩

/--
theorem `cofinite.bliminf_set_eq` / 定理 `cofinite.bliminf_set_eq`

English:
theorem cofinite.bliminf_set_eq
  statement: bliminf s cofinite p = { x | { n | p n ∧ x ∉ s n }.Finite }
  proof: by
  rw [← compl_inj_iff]
  simp only [bliminf_eq_iSup_biInf, compl_iInf, compl_iSup, ← blimsup_eq_iInf_biSup,
    cofinite.blimsup_set_eq]
  rfl

中文:
定理 cofinite.bliminf_set_eq
  结论: bliminf s cofinite p = { x | { n | p n ∧ x ∉ s n }.有限 }
  证明: by
  rw [← compl_inj_iff]
  simp only [bliminf_eq_iSup_biInf, compl_iInf, compl_iSup, ← blimsup_eq_iInf_biSup,
    cofinite.blimsup_set_eq]
  rfl

Depends on / 依赖: bliminf_eq_iSup_biInf, blimsup_eq_iInf_biSup, blimsup_set_eq, cofinite, cofinite.blimsup_set_eq, compl_iInf, compl_iSup, compl_inj_iff
-/
theorem cofinite.bliminf_set_eq : bliminf s cofinite p = { x | { n | p n ∧ x ∉ s n }.Finite } := by
  rw [← compl_inj_iff]
  simp only [bliminf_eq_iSup_biInf, compl_iInf, compl_iSup, ← blimsup_eq_iInf_biSup,
    cofinite.blimsup_set_eq]
  rfl

/--
theorem `cofinite.limsup_set_eq` / 定理 `cofinite.limsup_set_eq`

English:
theorem cofinite.limsup_set_eq
  statement: limsup s cofinite = { x | { n | x in s n }.Infinite }
  proof: by
  simp only [← cofinite.blimsup_true s, cofinite.blimsup_set_eq, true_and]

中文:
定理 cofinite.limsup_set_eq
  结论: limsup s cofinite = { x | { n | x in s n }.无限 }
  证明: by
  simp only [← cofinite.blimsup_true s, cofinite.blimsup_set_eq, true_and]

Depends on / 依赖: blimsup_set_eq, blimsup_true, cofinite, cofinite.blimsup_set_eq, cofinite.blimsup_true, true_and
-/
theorem cofinite.limsup_set_eq : limsup s cofinite = { x | { n | x in s n }.Infinite } := by
  simp only [← cofinite.blimsup_true s, cofinite.blimsup_set_eq, true_and]

/--
theorem `cofinite.liminf_set_eq` / 定理 `cofinite.liminf_set_eq`

English:
theorem cofinite.liminf_set_eq
  statement: liminf s cofinite = { x | { n | x ∉ s n }.Finite }
  proof: by
  simp only [← cofinite.bliminf_true s, cofinite.bliminf_set_eq, true_and]

中文:
定理 cofinite.liminf_set_eq
  结论: liminf s cofinite = { x | { n | x ∉ s n }.有限 }
  证明: by
  simp only [← cofinite.bliminf_true s, cofinite.bliminf_set_eq, true_and]

Depends on / 依赖: bliminf_set_eq, bliminf_true, cofinite, cofinite.bliminf_set_eq, cofinite.bliminf_true, true_and
-/
theorem cofinite.liminf_set_eq : liminf s cofinite = { x | { n | x ∉ s n }.Finite } := by
  simp only [← cofinite.bliminf_true s, cofinite.bliminf_set_eq, true_and]

/--
theorem `exists_forall_mem_of_hasBasis_mem_blimsup` / 定理 `exists_forall_mem_of_hasBasis_mem_blimsup`

English:
theorem exists_forall_mem_of_hasBasis_mem_blimsup
  statement: {l : Filter β} {b : ι -> Set β} {q : ι -> Prop}
  proof: by
  rw [blimsup_eq_iInf_biSup] at hx
  simp only [iSup_eq_iUnion, iInf_eq_iInter, mem_iInter, mem_iUnion, exists_prop] at hx
  choose g hg hg' using hx
  refine ⟨fun i : { i | q i } => g (b i) (hl.mem_of_mem i.2), fun i => ⟨?_, ?_⟩⟩
  · exact hg' (b i) (hl.mem_of_mem i.2)
  · exact hg (b i) (hl.mem

中文:
定理 存在_对任意_mem_of_hasBasis_mem_blimsup
  结论: {l : 滤子 β} {b : ι -> 集合 β} {q : ι -> 命题}
  证明: by
  rw [blimsup_eq_iInf_biSup] at hx
  simp only [iSup_eq_iUnion, iInf_eq_iInter, mem_iInter, mem_iUnion, exists_prop] at hx
  choose g hg hg' using hx
  refine ⟨fun i : { i | q i } => g (b i) (hl.mem_of_mem i.2), fun i => ⟨?_, ?_⟩⟩
  · exact hg' (b i) (hl.mem_of_mem i.2)
  · exact hg (b i) (hl.mem

Depends on / 依赖: blimsup_eq_iInf_biSup, exists_prop, hl.mem_of_mem, iInf_eq_iInter, iSup_eq_iUnion, mem_iInter, mem_iUnion, mem_of_mem
-/
theorem exists_forall_mem_of_hasBasis_mem_blimsup {l : Filter β} {b : ι -> Set β} {q : ι -> Prop}
    (hl : l.HasBasis q b) {u : β -> Set α} {p : β -> Prop} {x : α} (hx : x in blimsup u l p) :
    exists f : { i | q i } -> β, forall i, x in u (f i) ∧ p (f i) ∧ f i in b i := by
  rw [blimsup_eq_iInf_biSup] at hx
  simp only [iSup_eq_iUnion, iInf_eq_iInter, mem_iInter, mem_iUnion, exists_prop] at hx
  choose g hg hg' using hx
  refine ⟨fun i : { i | q i } => g (b i) (hl.mem_of_mem i.2), fun i => ⟨?_, ?_⟩⟩
  · exact hg' (b i) (hl.mem_of_mem i.2)
  · exact hg (b i) (hl.mem_of_mem i.2)

/--
theorem `exists_forall_mem_of_hasBasis_mem_blimsup'` / 定理 `exists_forall_mem_of_hasBasis_mem_blimsup'`

English:
theorem exists_forall_mem_of_hasBasis_mem_blimsup'
  statement: {l : Filter β} {b : ι -> Set β}
  proof: by
  obtain ⟨f, hf⟩ := exists_forall_mem_of_hasBasis_mem_blimsup hl hx
  exact ⟨fun i => f ⟨i, trivial⟩, fun i => hf ⟨i, trivial⟩⟩

中文:
定理 存在_对任意_mem_of_hasBasis_mem_blimsup'
  结论: {l : 滤子 β} {b : ι -> 集合 β}
  证明: by
  obtain ⟨f, hf⟩ := exists_forall_mem_of_hasBasis_mem_blimsup hl hx
  exact ⟨fun i => f ⟨i, trivial⟩, fun i => hf ⟨i, trivial⟩⟩

Depends on / 依赖: exists_forall_mem_of_hasBasis_mem_blimsup
-/
theorem exists_forall_mem_of_hasBasis_mem_blimsup' {l : Filter β} {b : ι -> Set β}
    (hl : l.HasBasis (fun _ => True) b) {u : β -> Set α} {p : β -> Prop} {x : α}
    (hx : x in blimsup u l p) : exists f : ι -> β, forall i, x in u (f i) ∧ p (f i) ∧ f i in b i := by
  obtain ⟨f, hf⟩ := exists_forall_mem_of_hasBasis_mem_blimsup hl hx
  exact ⟨fun i => f ⟨i, trivial⟩, fun i => hf ⟨i, trivial⟩⟩

end SetLattice

section ConditionallyCompleteLinearOrder

/--
theorem `frequently_lt_of_lt_limsSup` / 定理 `frequently_lt_of_lt_limsSup`

English:
theorem frequently_lt_of_lt_limsSup
  statement: {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
  proof: by
  contrapose! h
  exact limsSup_le_of_le hf h

中文:
定理 frequently_lt_of_lt_limsSup
  结论: {f : 滤子 α} [条件完备线性序 α] {a : α}
  证明: by
  contrapose! h
  exact limsSup_le_of_le hf h

Depends on / 依赖: contrapose, isBoundedDefault, limsSup, limsSup_le_of_le
-/
theorem frequently_lt_of_lt_limsSup {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
    (hf : f.IsCobounded (· <= ·) := by isBoundedDefault)
    (h : a < limsSup f) : existsᶠ n in f, a < n := by
  contrapose! h
  exact limsSup_le_of_le hf h

/--
theorem `frequently_lt_of_limsInf_lt` / 定理 `frequently_lt_of_limsInf_lt`

English:
theorem frequently_lt_of_limsInf_lt
  statement: {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
  proof: frequently_lt_of_lt_limsSup (α := OrderDual α) hf h

中文:
定理 frequently_lt_of_limsInf_lt
  结论: {f : 滤子 α} [条件完备线性序 α] {a : α}
  证明: frequently_lt_of_lt_limsSup (α := OrderDual α) hf h

Depends on / 依赖: OrderDual, frequently_lt_of_lt_limsSup, isBoundedDefault, limsInf
-/
theorem frequently_lt_of_limsInf_lt {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
    (hf : f.IsCobounded (· >= ·) := by isBoundedDefault)
    (h : limsInf f < a) : existsᶠ n in f, n < a :=
  frequently_lt_of_lt_limsSup (α := OrderDual α) hf h

/--
theorem `eventually_lt_of_lt_liminf` / 定理 `eventually_lt_of_lt_liminf`

English:
theorem eventually_lt_of_lt_liminf
  statement: {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α -> β}
  proof: by
  obtain ⟨c, hc, hbc⟩ : exists (c : β) (_ : c in { c : β | forallᶠ n : α in f, c <= u n }), b < c := by
    simp_rw [exists_prop]
    exact exists_lt_of_lt_csSup hu h
  exact hc.mono fun x hx => lt_of_lt_of_le hbc hx

中文:
定理 eventually_lt_of_lt_liminf
  结论: {f : 滤子 α} [条件完备线性序 β] {u : α -> β}
  证明: by
  obtain ⟨c, hc, hbc⟩ : exists (c : β) (_ : c in { c : β | forallᶠ n : α in f, c <= u n }), b < c := by
    simp_rw [exists_prop]
    exact exists_lt_of_lt_csSup hu h
  exact hc.mono fun x hx => lt_of_lt_of_le hbc hx

Depends on / 依赖: exists_lt_of_lt_csSup, exists_prop, hc.mono, isBoundedDefault, lt_of_lt_of_le, simp_rw
-/
theorem eventually_lt_of_lt_liminf {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α -> β}
    {b : β} (h : b < liminf u f)
    (hu : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault) :
    forallᶠ a in f, b < u a := by
  obtain ⟨c, hc, hbc⟩ : exists (c : β) (_ : c in { c : β | forallᶠ n : α in f, c <= u n }), b < c := by
    simp_rw [exists_prop]
    exact exists_lt_of_lt_csSup hu h
  exact hc.mono fun x hx => lt_of_lt_of_le hbc hx

/--
theorem `eventually_lt_of_limsup_lt` / 定理 `eventually_lt_of_limsup_lt`

English:
theorem eventually_lt_of_limsup_lt
  statement: {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α -> β}
  proof: eventually_lt_of_lt_liminf (β := βᵒᵈ) h hu

中文:
定理 eventually_lt_of_limsup_lt
  结论: {f : 滤子 α} [条件完备线性序 β] {u : α -> β}
  证明: eventually_lt_of_lt_liminf (β := βᵒᵈ) h hu

Depends on / 依赖: eventually_lt_of_lt_liminf, isBoundedDefault
-/
theorem eventually_lt_of_limsup_lt {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α -> β}
    {b : β} (h : limsup u f < b)
    (hu : f.IsBoundedUnder (· <= ·) u := by isBoundedDefault) :
    forallᶠ a in f, u a < b :=
  eventually_lt_of_lt_liminf (β := βᵒᵈ) h hu

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α]

/--
theorem `eventually_lt_add_pos_of_limsup_le` / 定理 `eventually_lt_add_pos_of_limsup_le`

English:
theorem eventually_lt_add_pos_of_limsup_le
  statement: [Preorder β] [AddZeroClass α] [AddLeftStrictMono α]
  proof: eventually_lt_of_limsup_lt (lt_of_le_of_lt hu (lt_add_of_pos_right x hε)) hu_bdd

中文:
定理 eventually_lt_add_pos_of_limsup_le
  结论: [预序 β] [加法零类 α] [AddLeftStrictMono α]
  证明: eventually_lt_of_limsup_lt (lt_of_le_of_lt hu (lt_add_of_pos_right x hε)) hu_bdd

Depends on / 依赖: eventually_lt_of_limsup_lt, hu_bdd, lt_add_of_pos_right, lt_of_le_of_lt
-/
theorem eventually_lt_add_pos_of_limsup_le [Preorder β] [AddZeroClass α] [AddLeftStrictMono α]
    {x ε : α} {u : β -> α} (hu_bdd : IsBoundedUnder LE.le atTop u) (hu : Filter.limsup u atTop <= x)
    (hε : 0 < ε) :
    forallᶠ b : β in atTop, u b < x + ε :=
  eventually_lt_of_limsup_lt (lt_of_le_of_lt hu (lt_add_of_pos_right x hε)) hu_bdd

/--
theorem `eventually_add_neg_lt_of_le_liminf` / 定理 `eventually_add_neg_lt_of_le_liminf`

English:
theorem eventually_add_neg_lt_of_le_liminf
  statement: [Preorder β] [AddZeroClass α] [AddLeftStrictMono α]
  proof: eventually_lt_of_lt_liminf (lt_of_lt_of_le (add_lt_of_neg_right x hε) hu) hu_bdd

中文:
定理 eventually_add_neg_lt_of_le_liminf
  结论: [预序 β] [加法零类 α] [AddLeftStrictMono α]
  证明: eventually_lt_of_lt_liminf (lt_of_lt_of_le (add_lt_of_neg_right x hε) hu) hu_bdd

Depends on / 依赖: add_lt_of_neg_right, eventually_lt_of_lt_liminf, hu_bdd, lt_of_lt_of_le
-/
theorem eventually_add_neg_lt_of_le_liminf [Preorder β] [AddZeroClass α] [AddLeftStrictMono α]
    {x ε : α} {u : β -> α} (hu_bdd : IsBoundedUnder GE.ge atTop u) (hu : x <= Filter.liminf u atTop)
    (hε : ε < 0) :
    forallᶠ b : β in atTop, x + ε < u b :=
  eventually_lt_of_lt_liminf (lt_of_lt_of_le (add_lt_of_neg_right x hε) hu) hu_bdd

/--
theorem `exists_lt_of_limsup_le` / 定理 `exists_lt_of_limsup_le`

English:
theorem exists_lt_of_limsup_le
  statement: [AddZeroClass α] [AddLeftStrictMono α] {x ε : α} {u : Nat -> α}
  proof: by
  have h : forallᶠ n : Nat in atTop, u n < x + ε := eventually_lt_add_pos_of_limsup_le hu_bdd hu hε
  simp only [eventually_atTop] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨⟨n + 1, Nat.succ_pos _⟩, hn (n + 1) (Nat.le_succ _)⟩

中文:
定理 存在_lt_of_limsup_le
  结论: [加法零类 α] [AddLeftStrictMono α] {x ε : α} {u : 自然数 -> α}
  证明: by
  have h : forallᶠ n : Nat in atTop, u n < x + ε := eventually_lt_add_pos_of_limsup_le hu_bdd hu hε
  simp only [eventually_atTop] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨⟨n + 1, Nat.succ_pos _⟩, hn (n + 1) (Nat.le_succ _)⟩

Depends on / 依赖: Nat.le_succ, Nat.succ_pos, eventually_atTop, eventually_lt_add_pos_of_limsup_le, hu_bdd, le_succ, succ_pos
-/
theorem exists_lt_of_limsup_le [AddZeroClass α] [AddLeftStrictMono α] {x ε : α} {u : Nat -> α}
    (hu_bdd : IsBoundedUnder LE.le atTop u) (hu : Filter.limsup u atTop <= x) (hε : 0 < ε) :
    exists n : PNat, u n < x + ε := by
  have h : forallᶠ n : Nat in atTop, u n < x + ε := eventually_lt_add_pos_of_limsup_le hu_bdd hu hε
  simp only [eventually_atTop] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨⟨n + 1, Nat.succ_pos _⟩, hn (n + 1) (Nat.le_succ _)⟩

/--
theorem `exists_lt_of_le_liminf` / 定理 `exists_lt_of_le_liminf`

English:
theorem exists_lt_of_le_liminf
  statement: [AddZeroClass α] [AddLeftStrictMono α] {x ε : α} {u : Nat -> α}
  proof: by
  have h : forallᶠ n : Nat in atTop, x + ε < u n := eventually_add_neg_lt_of_le_liminf hu_bdd hu hε
  simp only [eventually_atTop] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨⟨n + 1, Nat.succ_pos _⟩, hn (n + 1) (Nat.le_succ _)⟩

中文:
定理 存在_lt_of_le_liminf
  结论: [加法零类 α] [AddLeftStrictMono α] {x ε : α} {u : 自然数 -> α}
  证明: by
  have h : forallᶠ n : Nat in atTop, x + ε < u n := eventually_add_neg_lt_of_le_liminf hu_bdd hu hε
  simp only [eventually_atTop] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨⟨n + 1, Nat.succ_pos _⟩, hn (n + 1) (Nat.le_succ _)⟩

Depends on / 依赖: Nat.le_succ, Nat.succ_pos, eventually_add_neg_lt_of_le_liminf, eventually_atTop, hu_bdd, le_succ, succ_pos
-/
theorem exists_lt_of_le_liminf [AddZeroClass α] [AddLeftStrictMono α] {x ε : α} {u : Nat -> α}
    (hu_bdd : IsBoundedUnder GE.ge atTop u) (hu : x <= Filter.liminf u atTop) (hε : ε < 0) :
    exists n : PNat, x + ε < u n := by
  have h : forallᶠ n : Nat in atTop, x + ε < u n := eventually_add_neg_lt_of_le_liminf hu_bdd hu hε
  simp only [eventually_atTop] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨⟨n + 1, Nat.succ_pos _⟩, hn (n + 1) (Nat.le_succ _)⟩
end ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α -> β}

/--
theorem `frequently_lt_of_lt_limsup` / 定理 `frequently_lt_of_lt_limsup`

English:
theorem frequently_lt_of_lt_limsup
  statement: {b : β}
  proof: by
  contrapose! h
  apply limsSup_le_of_le hu
  simpa using h

中文:
定理 frequently_lt_of_lt_limsup
  结论: {b : β}
  证明: by
  contrapose! h
  apply limsSup_le_of_le hu
  simpa using h

Depends on / 依赖: contrapose, isBoundedDefault, limsSup_le_of_le, limsup
-/
theorem frequently_lt_of_lt_limsup {b : β}
    (hu : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
    (h : b < limsup u f) : existsᶠ x in f, b < u x := by
  contrapose! h
  apply limsSup_le_of_le hu
  simpa using h

/--
theorem `frequently_lt_of_liminf_lt` / 定理 `frequently_lt_of_liminf_lt`

English:
theorem frequently_lt_of_liminf_lt
  statement: {b : β}
  proof: frequently_lt_of_lt_limsup (β := βᵒᵈ) hu h

中文:
定理 frequently_lt_of_liminf_lt
  结论: {b : β}
  证明: frequently_lt_of_lt_limsup (β := βᵒᵈ) hu h

Depends on / 依赖: frequently_lt_of_lt_limsup, isBoundedDefault, liminf
-/
theorem frequently_lt_of_liminf_lt {b : β}
    (hu : f.IsCoboundedUnder (· >= ·) u := by isBoundedDefault)
    (h : liminf u f < b) : existsᶠ x in f, u x < b :=
  frequently_lt_of_lt_limsup (β := βᵒᵈ) hu h

/--
theorem `limsup_le_iff` / 定理 `limsup_le_iff`

English:
theorem limsup_le_iff
  statement: {x : β} (h₁ : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
  proof: by
  refine ⟨fun h _ h' => eventually_lt_of_limsup_lt (h.trans_lt h') h₂, fun h => ?_⟩
  --Two cases: Either `x` is a cluster point from above, or it is not.
  --In the first case, we use `forall_gt_iff_le` and split an interval.
  --In the second case, the function `u` must eventually be smaller or

中文:
定理 limsup_le_iff
  结论: {x : β} (h₁ : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
  证明: by
  refine ⟨fun h _ h' => eventually_lt_of_limsup_lt (h.trans_lt h') h₂, fun h => ?_⟩
  --Two cases: Either `x` is a cluster point from above, or it is not.
  --In the first case, we use `forall_gt_iff_le` and split an interval.
  --In the second case, the function `u` must eventually be smaller or

Depends on / 依赖: IsBoundedUnder, eventually_lt_of_limsup_lt, f.IsBoundedUnder, h.trans_lt, isBoundedDefault, limsup, trans_lt
-/
theorem limsup_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· <= ·) u := by isBoundedDefault) :
    limsup u f <= x ↔ forall y > x, forallᶠ a in f, u a < y := by
  refine ⟨fun h _ h' => eventually_lt_of_limsup_lt (h.trans_lt h') h₂, fun h => ?_⟩
  --Two cases: Either `x` is a cluster point from above, or it is not.
  --In the first case, we use `forall_gt_iff_le` and split an interval.
  --In the second case, the function `u` must eventually be smaller or equal to `x`.
  by_cases h' : forall y > x, exists z, x < z ∧ z < y
  · rw [← forall_gt_iff_le]
    intro y x_y
    rcases h' y x_y with ⟨z, x_z, z_y⟩
    exact (limsup_le_of_le h₁ ((h z x_z).mono (fun _ => le_of_lt))).trans_lt z_y
  · apply limsup_le_of_le h₁
    push +distrib Not at h'
    rcases h' with ⟨z, x_z, hz⟩
exact (h z x_z).mono fun w hw => (or_iff_left (not_le_of_gt hw)).1 (hz (u w))

/--
lemma `limsup_le_iff'` / 引理 `limsup_le_iff'`

English:
lemma limsup_le_iff'
  statement: [DenselyOrdered β] {x : β}
  proof: by
  refine ⟨fun h _ h' => (eventually_lt_of_limsup_lt (h.trans_lt h') h₂).mono fun _ => le_of_lt, ?_⟩
  rw [← forall_gt_iff_le]
  intro h y x_y
  obtain ⟨z, x_z, z_y⟩ := exists_between x_y
  exact (limsup_le_of_le h₁ (h z x_z)).trans_lt z_y

中文:
引理 limsup_le_iff'
  结论: [稠密序 β] {x : β}
  证明: by
  refine ⟨fun h _ h' => (eventually_lt_of_limsup_lt (h.trans_lt h') h₂).mono fun _ => le_of_lt, ?_⟩
  rw [← forall_gt_iff_le]
  intro h y x_y
  obtain ⟨z, x_z, z_y⟩ := exists_between x_y
  exact (limsup_le_of_le h₁ (h z x_z)).trans_lt z_y

Depends on / 依赖: IsBoundedUnder, eventually_lt_of_limsup_lt, exists_between, forall_gt_iff_le, h.trans_lt, isBoundedDefault, le_of_lt, limsup, limsup_le_of_le, trans_lt
-/
lemma limsup_le_iff' [DenselyOrdered β] {x : β}
    (h₁ : IsCoboundedUnder (· <= ·) f u := by isBoundedDefault)
    (h₂ : IsBoundedUnder (· <= ·) f u := by isBoundedDefault) :
    limsup u f <= x ↔ forall y > x, forallᶠ (a : α) in f, u a <= y := by
  refine ⟨fun h _ h' => (eventually_lt_of_limsup_lt (h.trans_lt h') h₂).mono fun _ => le_of_lt, ?_⟩
  rw [← forall_gt_iff_le]
  intro h y x_y
  obtain ⟨z, x_z, z_y⟩ := exists_between x_y
  exact (limsup_le_of_le h₁ (h z x_z)).trans_lt z_y

/--
theorem `le_limsup_iff` / 定理 `le_limsup_iff`

English:
theorem le_limsup_iff
  statement: {x : β} (h₁ : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
  proof: by
  refine ⟨fun h _ h' => frequently_lt_of_lt_limsup h₁ (h'.trans_le h), fun h => ?_⟩
  --Two cases: Either `x` is a cluster point from below, or it is not.
  --In the first case, we use `forall_lt_iff_le` and split an interval.
  --In the second case, the function `u` must frequently be larger or 

中文:
定理 le_limsup_iff
  结论: {x : β} (h₁ : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
  证明: by
  refine ⟨fun h _ h' => frequently_lt_of_lt_limsup h₁ (h'.trans_le h), fun h => ?_⟩
  --Two cases: Either `x` is a cluster point from below, or it is not.
  --In the first case, we use `forall_lt_iff_le` and split an interval.
  --In the second case, the function `u` must frequently be larger or 

Depends on / 依赖: IsBoundedUnder, f.IsBoundedUnder, frequently_lt_of_lt_limsup, isBoundedDefault, limsup, trans_le
-/
theorem le_limsup_iff {x : β} (h₁ : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· <= ·) u := by isBoundedDefault) :
    x <= limsup u f ↔ forall y < x, existsᶠ a in f, y < u a := by
  refine ⟨fun h _ h' => frequently_lt_of_lt_limsup h₁ (h'.trans_le h), fun h => ?_⟩
  --Two cases: Either `x` is a cluster point from below, or it is not.
  --In the first case, we use `forall_lt_iff_le` and split an interval.
  --In the second case, the function `u` must frequently be larger or equal to `x`.
  by_cases h' : forall y < x, exists z, y < z ∧ z < x
  · rw [← forall_lt_iff_le]
    intro y y_x
    obtain ⟨z, y_z, z_x⟩ := h' y y_x
    exact y_z.trans_le (le_limsup_of_frequently_le ((h z z_x).mono (fun _ => le_of_lt)) h₂)
  · apply le_limsup_of_frequently_le _ h₂
    push +distrib Not at h'
    rcases h' with ⟨z, z_x, hz⟩
exact (h z z_x).mono fun w hw => (or_iff_right (not_le_of_gt hw)).1 (hz (u w))

/--
lemma `le_limsup_iff'` / 引理 `le_limsup_iff'`

English:
lemma le_limsup_iff'
  statement: [DenselyOrdered β] {x : β}
  proof: by
  refine ⟨fun h _ h' => (frequently_lt_of_lt_limsup h₁ (h'.trans_le h)).mono fun _ => le_of_lt, ?_⟩
  rw [← forall_lt_iff_le]
  intro h y y_x
  obtain ⟨z, y_z, z_x⟩ := exists_between y_x
  exact y_z.trans_le (le_limsup_of_frequently_le (h z z_x) h₂)

中文:
引理 le_limsup_iff'
  结论: [稠密序 β] {x : β}
  证明: by
  refine ⟨fun h _ h' => (frequently_lt_of_lt_limsup h₁ (h'.trans_le h)).mono fun _ => le_of_lt, ?_⟩
  rw [← forall_lt_iff_le]
  intro h y y_x
  obtain ⟨z, y_z, z_x⟩ := exists_between y_x
  exact y_z.trans_le (le_limsup_of_frequently_le (h z z_x) h₂)

Depends on / 依赖: IsBoundedUnder, exists_between, f.IsBoundedUnder, forall_lt_iff_le, frequently_lt_of_lt_limsup, isBoundedDefault, le_limsup_of_frequently_le, le_of_lt, limsup, trans_le, y_z.trans_le
-/
lemma le_limsup_iff' [DenselyOrdered β] {x : β}
    (h₁ : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· <= ·) u := by isBoundedDefault) :
    x <= limsup u f ↔ forall y < x, existsᶠ a in f, y <= u a := by
  refine ⟨fun h _ h' => (frequently_lt_of_lt_limsup h₁ (h'.trans_le h)).mono fun _ => le_of_lt, ?_⟩
  rw [← forall_lt_iff_le]
  intro h y y_x
  obtain ⟨z, y_z, z_x⟩ := exists_between y_x
  exact y_z.trans_le (le_limsup_of_frequently_le (h z z_x) h₂)

/--
theorem `le_liminf_iff` / 定理 `le_liminf_iff`

English:
theorem le_liminf_iff
  statement: {x : β} (h₁ : f.IsCoboundedUnder (· >= ·) u := by isBoundedDefault)
  proof: limsup_le_iff (β := βᵒᵈ) h₁ h₂

中文:
定理 le_liminf_iff
  结论: {x : β} (h₁ : f.IsCoboundedUnder (· >= ·) u := by isBoundedDefault)
  证明: limsup_le_iff (β := βᵒᵈ) h₁ h₂

Depends on / 依赖: IsBoundedUnder, f.IsBoundedUnder, isBoundedDefault, liminf, limsup_le_iff
-/
theorem le_liminf_iff {x : β} (h₁ : f.IsCoboundedUnder (· >= ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault) :
    x <= liminf u f ↔ forall y < x, forallᶠ a in f, y < u a := limsup_le_iff (β := βᵒᵈ) h₁ h₂

/--
theorem `le_liminf_iff'` / 定理 `le_liminf_iff'`

English:
theorem le_liminf_iff'
  statement: [DenselyOrdered β] {x : β}
  proof: limsup_le_iff' (β := βᵒᵈ) h₁ h₂

中文:
定理 le_liminf_iff'
  结论: [稠密序 β] {x : β}
  证明: limsup_le_iff' (β := βᵒᵈ) h₁ h₂

Depends on / 依赖: IsBoundedUnder, f.IsBoundedUnder, isBoundedDefault, liminf, limsup_le_iff
-/
theorem le_liminf_iff' [DenselyOrdered β] {x : β}
    (h₁ : f.IsCoboundedUnder (· >= ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault) :
    x <= liminf u f ↔ forall y < x, forallᶠ a in f, y <= u a := limsup_le_iff' (β := βᵒᵈ) h₁ h₂

/--
theorem `liminf_le_iff` / 定理 `liminf_le_iff`

English:
theorem liminf_le_iff
  statement: {x : β} (h₁ : f.IsCoboundedUnder (· >= ·) u := by isBoundedDefault)
  proof: le_limsup_iff (β := βᵒᵈ) h₁ h₂

中文:
定理 liminf_le_iff
  结论: {x : β} (h₁ : f.IsCoboundedUnder (· >= ·) u := by isBoundedDefault)
  证明: le_limsup_iff (β := βᵒᵈ) h₁ h₂

Depends on / 依赖: IsBoundedUnder, f.IsBoundedUnder, isBoundedDefault, le_limsup_iff, liminf
-/
theorem liminf_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· >= ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault) :
    liminf u f <= x ↔ forall y > x, existsᶠ a in f, u a < y := le_limsup_iff (β := βᵒᵈ) h₁ h₂

/--
theorem `liminf_le_iff'` / 定理 `liminf_le_iff'`

English:
theorem liminf_le_iff'
  statement: [DenselyOrdered β] {x : β}
  proof: le_limsup_iff' (β := βᵒᵈ) h₁ h₂

中文:
定理 liminf_le_iff'
  结论: [稠密序 β] {x : β}
  证明: le_limsup_iff' (β := βᵒᵈ) h₁ h₂

Depends on / 依赖: IsBoundedUnder, f.IsBoundedUnder, isBoundedDefault, le_limsup_iff, liminf
-/
theorem liminf_le_iff' [DenselyOrdered β] {x : β}
    (h₁ : f.IsCoboundedUnder (· >= ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault) :
    liminf u f <= x ↔ forall y > x, existsᶠ a in f, u a <= y := le_limsup_iff' (β := βᵒᵈ) h₁ h₂

/--
lemma `liminf_le_limsup_of_frequently_le` / 引理 `liminf_le_limsup_of_frequently_le`

English:
lemma liminf_le_limsup_of_frequently_le
  statement: {v : α -> β} (h : existsᶠ x in f, u x <= v x)
  proof: by
  rcases f.eq_or_neBot with rfl | _
  · exact (frequently_bot h).rec
  have h₃ : f.IsCoboundedUnder (· >= ·) u := by
    obtain ⟨a, ha⟩ := h₂.eventually_le
    apply IsCoboundedUnder.of_frequently_le (a := a)
    exact (h.and_eventually ha).mono fun x ⟨u_x, v_x⟩ => u_x.trans v_x
  have h₄ : f.IsC

中文:
引理 liminf_le_limsup_of_frequently_le
  结论: {v : α -> β} (h : 存在ᶠ x in f, u x <= v x)
  证明: by
  rcases f.eq_or_neBot with rfl | _
  · exact (frequently_bot h).rec
  have h₃ : f.IsCoboundedUnder (· >= ·) u := by
    obtain ⟨a, ha⟩ := h₂.eventually_le
    apply IsCoboundedUnder.of_frequently_le (a := a)
    exact (h.and_eventually ha).mono fun x ⟨u_x, v_x⟩ => u_x.trans v_x
  have h₄ : f.IsC

Depends on / 依赖: IsBoundedUnder, IsCoboundedUnder, IsCoboundedUnder.of_frequently_ge, IsCoboundedUnder.of_frequently_le, and_eventually, eq_or_neBot, eventually_ge, eventually_le, f.IsBoundedUnder, f.IsCoboundedUnder, f.eq_or_neBot, frequently_bot, h.and_eventually, isBoundedDefault, liminf, limsup, of_frequently_ge, of_frequently_le, u_x.trans
-/
lemma liminf_le_limsup_of_frequently_le {v : α -> β} (h : existsᶠ x in f, u x <= v x)
    (h₁ : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· <= ·) v := by isBoundedDefault) :
    liminf u f <= limsup v f := by
  rcases f.eq_or_neBot with rfl | _
  · exact (frequently_bot h).rec
  have h₃ : f.IsCoboundedUnder (· >= ·) u := by
    obtain ⟨a, ha⟩ := h₂.eventually_le
    apply IsCoboundedUnder.of_frequently_le (a := a)
    exact (h.and_eventually ha).mono fun x ⟨u_x, v_x⟩ => u_x.trans v_x
  have h₄ : f.IsCoboundedUnder (· <= ·) v := by
    obtain ⟨a, ha⟩ := h₁.eventually_ge
    apply IsCoboundedUnder.of_frequently_ge (a := a)
    exact (ha.and_frequently h).mono fun x ⟨u_x, v_x⟩ => u_x.trans v_x
  refine (le_limsup_iff h₄ h₂).2 fun y y_v => ?_
  have := (le_liminf_iff h₃ h₁).1 (le_refl (liminf u f)) y y_v
  exact (h.and_eventually this).mono fun x ⟨ux_vx, y_ux⟩ => y_ux.trans_le ux_vx

variable [ConditionallyCompleteLinearOrder α] {f : Filter α} {b : α}

-- The linter erroneously claims that I'm not referring to `c`
set_option linter.unusedVariables false in
/--
theorem `lt_mem_sets_of_limsSup_lt` / 定理 `lt_mem_sets_of_limsSup_lt`

English:
theorem lt_mem_sets_of_limsSup_lt
  given: (h : f.IsBounded (· <= ·)) (l : f.limsSup < b)
  proof: let ⟨c, (h : forallᶠ a in f, a <= c), hcb⟩ := exists_lt_of_csInf_lt h l
  mem_of_superset h fun _a => hcb.trans_le'

中文:
定理 lt_mem_sets_of_limsSup_lt
  条件: (h : f.IsBounded (· <= ·)) (l : f.limsSup < b)
  证明: let ⟨c, (h : forallᶠ a in f, a <= c), hcb⟩ := exists_lt_of_csInf_lt h l
  mem_of_superset h fun _a => hcb.trans_le'

Depends on / 依赖: exists_lt_of_csInf_lt, hcb.trans_le, mem_of_superset, trans_le
-/
theorem lt_mem_sets_of_limsSup_lt (h : f.IsBounded (· <= ·)) (l : f.limsSup < b) :
    forallᶠ a in f, a < b :=
  let ⟨c, (h : forallᶠ a in f, a <= c), hcb⟩ := exists_lt_of_csInf_lt h l
  mem_of_superset h fun _a => hcb.trans_le'

/--
theorem `gt_mem_sets_of_limsInf_gt` / 定理 `gt_mem_sets_of_limsInf_gt`

English:
theorem gt_mem_sets_of_limsInf_gt
  statement: f.IsBounded (· >= ·) -> b < f.limsInf -> forallᶠ a in f, b < a
  proof: @lt_mem_sets_of_limsSup_lt αᵒᵈ _ _ _

中文:
定理 gt_mem_sets_of_limsInf_gt
  结论: f.IsBounded (· >= ·) -> b < f.limsInf -> 对任意ᶠ a in f, b < a
  证明: @lt_mem_sets_of_limsSup_lt αᵒᵈ _ _ _

Depends on / 依赖: lt_mem_sets_of_limsSup_lt
-/
theorem gt_mem_sets_of_limsInf_gt : f.IsBounded (· >= ·) -> b < f.limsInf -> forallᶠ a in f, b < a :=
  @lt_mem_sets_of_limsSup_lt αᵒᵈ _ _ _

section Classical

open scoped Classical in
/--
Definition of `liminfReparam` / `liminfReparam` 的定义

English:
definition liminfReparam
  body: let m : Set (Subtype p) := {j | BddBelow (range (fun (i : s j) => f i))}
  let g : Nat -> Subtype p := (exists_surjective_nat _).choose
  have Z : exists n, g n in m ∨ forall j, j ∉ m := by
    by_cases! H : exists j, j in m
    · rcases H with ⟨j, hj⟩
      rcases (exists_surjective_nat (Subtype p)

中文:
定义 liminfReparam
  定义体: let m : Set (Subtype p) := {j | BddBelow (range (fun (i : s j) => f i))}
  let g : Nat -> Subtype p := (exists_surjective_nat _).choose
  have Z : exists n, g n in m ∨ forall j, j ∉ m := by
    by_cases! H : exists j, j in m
    · rcases H with ⟨j, hj⟩
      rcases (exists_surjective_nat (Subtype p)

Depends on / 依赖: BddBelow, Nat.find, Or.inl, Or.inr, Subtype, choose_spec, exists_surjective_nat
-/
noncomputable def liminfReparam
    (f : ι -> α) (s : ι' -> Set ι) (p : ι' -> Prop) [Countable (Subtype p)] [Nonempty (Subtype p)]
    (j : Subtype p) : Subtype p :=
  let m : Set (Subtype p) := {j | BddBelow (range (fun (i : s j) => f i))}
  let g : Nat -> Subtype p := (exists_surjective_nat _).choose
  have Z : exists n, g n in m ∨ forall j, j ∉ m := by
    by_cases! H : exists j, j in m
    · rcases H with ⟨j, hj⟩
      rcases (exists_surjective_nat (Subtype p)).choose_spec j with ⟨n, rfl⟩
      exact ⟨n, Or.inl hj⟩
    · exact ⟨0, Or.inr H⟩
  if j in m then j else g (Nat.find Z)

@[deprecated (since := "2026-07-18")]
alias liminf_reparam := liminfReparam

/--
theorem `HasBasis.liminf_eq_ciSup_ciInf` / 定理 `HasBasis.liminf_eq_ciSup_ciInf`

English:
theorem HasBasis.liminf_eq_ciSup_ciInf
  statement: {v : Filter ι}
  proof: by
  classical
  rcases H with ⟨j0, hj0⟩
  let m : Set (Subtype p) := {j | BddBelow (range (fun (i : s j) => f i))}
  have : forall (j : Subtype p), Nonempty (s j) := fun j => Nonempty.coe_sort (hs j)
  have A : ⋃ (j : Subtype p), ⋂ (i : s j), Iic (f i) =
         ⋃ (j : Subtype p), ⋂ (i : s (liminf

中文:
定理 有基.liminf_eq_ciSup_ciInf
  结论: {v : 滤子 ι}
  证明: by
  classical
  rcases H with ⟨j0, hj0⟩
  let m : Set (Subtype p) := {j | BddBelow (range (fun (i : s j) => f i))}
  have : forall (j : Subtype p), Nonempty (s j) := fun j => Nonempty.coe_sort (hs j)
  have A : ⋃ (j : Subtype p), ⋂ (i : s j), Iic (f i) =
         ⋃ (j : Subtype p), ⋂ (i : s (liminf

Depends on / 依赖: BddBelow, Nonempty, Nonempty.coe_sort, Subset, Subset.antisymm, Subtype, antisymm, classical, coe_sort, conv_lhs, iUnion_subset, ite_true, liminfReparam
-/
theorem HasBasis.liminf_eq_ciSup_ciInf {v : Filter ι}
    {p : ι' -> Prop} {s : ι' -> Set ι} [Countable (Subtype p)] [Nonempty (Subtype p)]
    (hv : v.HasBasis p s) {f : ι -> α} (hs : forall (j : Subtype p), (s j).Nonempty)
    (H : exists (j : Subtype p), BddBelow (range (fun (i : s j) => f i))) :
    liminf f v = ⨆ (j : Subtype p), ⨅ (i : s (liminfReparam f s p j)), f i := by
  classical
  rcases H with ⟨j0, hj0⟩
  let m : Set (Subtype p) := {j | BddBelow (range (fun (i : s j) => f i))}
  have : forall (j : Subtype p), Nonempty (s j) := fun j => Nonempty.coe_sort (hs j)
  have A : ⋃ (j : Subtype p), ⋂ (i : s j), Iic (f i) =
         ⋃ (j : Subtype p), ⋂ (i : s (liminfReparam f s p j)), Iic (f i) := by
    apply Subset.antisymm
    · apply iUnion_subset (fun j => ?_)
      by_cases hj : j in m
      · have : j = liminfReparam f s p j := by simp only [m, liminfReparam, hj, ite_true]
        conv_lhs => rw [this]
        apply subset_iUnion _ j
      · simp only [m, mem_ofPred_eq, ← nonempty_iInter_Iic_iff, not_nonempty_iff_eq_empty] at hj
        simp only [hj, empty_subset]
    · apply iUnion_subset (fun j => ?_)
      exact subset_iUnion (fun (k : Subtype p) => (⋂ (i : s k), Iic (f i))) (liminfReparam f s p j)
  have B : forall (j : Subtype p), ⋂ (i : s (liminfReparam f s p j)), Iic (f i) =
                                Iic (⨅ (i : s (liminfReparam f s p j)), f i) := by
    intro j
    apply (Iic_ciInf _).symm
    change liminfReparam f s p j in m
    by_cases Hj : j in m
    · simpa only [m, liminfReparam, if_pos Hj] using Hj
    · simp only [m, liminfReparam, if_neg Hj]
      have Z : exists n, (exists_surjective_nat (Subtype p)).choose n in m ∨ forall j, j ∉ m := by
        rcases (exists_surjective_nat (Subtype p)).choose_spec j0 with ⟨n, rfl⟩
        exact ⟨n, Or.inl hj0⟩
      rcases Nat.find_spec Z with hZ | hZ
      · exact hZ
      · exact (hZ j0 hj0).elim
  simp_rw [hv.liminf_eq_sSup_iUnion_iInter, A, B, sSup_iUnion_Iic]

open scoped Classical in
/--
theorem `HasBasis.liminf_eq_ite` / 定理 `HasBasis.liminf_eq_ite`

English:
theorem HasBasis.liminf_eq_ite
  statement: {v : Filter ι} {p : ι' -> Prop} {s : ι' -> Set ι}
  proof: by
  by_cases H : exists (j : Subtype p), s j = ∅
  · rw [if_pos H]
    rcases H with ⟨j, hj⟩
    simp [hv.liminf_eq_sSup_univ_of_empty j j.2 hj]
  rw [if_neg H]
  by_cases H' : forall (j : Subtype p), ¬BddBelow (range (fun (i : s j) => f i))
  · have A : forall (j : Subtype p), ⋂ (i : s j), Iic (f 

中文:
定理 有基.liminf_eq_ite
  结论: {v : 滤子 ι} {p : ι' -> 命题} {s : ι' -> 集合 ι}
  证明: by
  by_cases H : exists (j : Subtype p), s j = ∅
  · rw [if_pos H]
    rcases H with ⟨j, hj⟩
    simp [hv.liminf_eq_sSup_univ_of_empty j j.2 hj]
  rw [if_neg H]
  by_cases H' : forall (j : Subtype p), ¬BddBelow (range (fun (i : s j) => f i))
  · have A : forall (j : Subtype p), ⋂ (i : s j), Iic (f 

Depends on / 依赖: BddBelow, Subtype, hv.liminf_eq_ciSup_ciInf, hv.liminf_eq_sSup_iUnion_iInter, hv.liminf_eq_sSup_univ_of_empty, iUnion_empty, if_neg, if_pos, liminf_eq_ciSup_ciInf, liminf_eq_sSup_iUnion_iInter, liminf_eq_sSup_univ_of_empty, nonempty_iInter_Iic_iff, not_nonempty_iff_eq_empty, simp_rw
-/
theorem HasBasis.liminf_eq_ite {v : Filter ι} {p : ι' -> Prop} {s : ι' -> Set ι}
    [Countable (Subtype p)] [Nonempty (Subtype p)] (hv : v.HasBasis p s) (f : ι -> α) :
    liminf f v = if exists (j : Subtype p), s j = ∅ then sSup univ else
      if forall (j : Subtype p), ¬BddBelow (range (fun (i : s j) => f i)) then sSup ∅
      else ⨆ (j : Subtype p), ⨅ (i : s (liminfReparam f s p j)), f i := by
  by_cases H : exists (j : Subtype p), s j = ∅
  · rw [if_pos H]
    rcases H with ⟨j, hj⟩
    simp [hv.liminf_eq_sSup_univ_of_empty j j.2 hj]
  rw [if_neg H]
  by_cases H' : forall (j : Subtype p), ¬BddBelow (range (fun (i : s j) => f i))
  · have A : forall (j : Subtype p), ⋂ (i : s j), Iic (f i) = ∅ := by
      simp_rw [← not_nonempty_iff_eq_empty, nonempty_iInter_Iic_iff]
      exact H'
    simp_rw [if_pos H', hv.liminf_eq_sSup_iUnion_iInter, A, iUnion_empty]
  rw [if_neg H']
  apply hv.liminf_eq_ciSup_ciInf
  · push Not at H
    simpa only [nonempty_iff_ne_empty] using H
  · push Not at H'
    exact H'

/--
Definition of `limsupReparam` / `limsupReparam` 的定义

English:
definition limsupReparam
  body: liminfReparam (α := αᵒᵈ) f s p j

@[deprecated (since := "2026-07-18")]
alias limsup_reparam := limsupReparam

中文:
定义 limsupReparam
  定义体: liminfReparam (α := αᵒᵈ) f s p j

@[deprecated (since := "2026-07-18")]
alias limsup_reparam := limsupReparam

Depends on / 依赖: liminfReparam
-/
noncomputable def limsupReparam
    (f : ι -> α) (s : ι' -> Set ι) (p : ι' -> Prop) [Countable (Subtype p)] [Nonempty (Subtype p)]
    (j : Subtype p) : Subtype p :=
  liminfReparam (α := αᵒᵈ) f s p j

@[deprecated (since := "2026-07-18")]
alias limsup_reparam := limsupReparam

/--
theorem `HasBasis.limsup_eq_ciInf_ciSup` / 定理 `HasBasis.limsup_eq_ciInf_ciSup`

English:
theorem HasBasis.limsup_eq_ciInf_ciSup
  statement: {v : Filter ι}
  proof: HasBasis.liminf_eq_ciSup_ciInf (α := αᵒᵈ) hv hs H

中文:
定理 有基.limsup_eq_ciInf_ciSup
  结论: {v : 滤子 ι}
  证明: HasBasis.liminf_eq_ciSup_ciInf (α := αᵒᵈ) hv hs H

Depends on / 依赖: HasBasis, HasBasis.liminf_eq_ciSup_ciInf, liminf_eq_ciSup_ciInf
-/
theorem HasBasis.limsup_eq_ciInf_ciSup {v : Filter ι}
    {p : ι' -> Prop} {s : ι' -> Set ι} [Countable (Subtype p)] [Nonempty (Subtype p)]
    (hv : v.HasBasis p s) {f : ι -> α} (hs : forall (j : Subtype p), (s j).Nonempty)
    (H : exists (j : Subtype p), BddAbove (range (fun (i : s j) => f i))) :
    limsup f v = ⨅ (j : Subtype p), ⨆ (i : s (limsupReparam f s p j)), f i :=
  HasBasis.liminf_eq_ciSup_ciInf (α := αᵒᵈ) hv hs H

open scoped Classical in
/--
theorem `HasBasis.limsup_eq_ite` / 定理 `HasBasis.limsup_eq_ite`

English:
theorem HasBasis.limsup_eq_ite
  statement: {v : Filter ι} {p : ι' -> Prop} {s : ι' -> Set ι}
  proof: HasBasis.liminf_eq_ite (α := αᵒᵈ) hv f

中文:
定理 有基.limsup_eq_ite
  结论: {v : 滤子 ι} {p : ι' -> 命题} {s : ι' -> 集合 ι}
  证明: HasBasis.liminf_eq_ite (α := αᵒᵈ) hv f

Depends on / 依赖: HasBasis, HasBasis.liminf_eq_ite, liminf_eq_ite
-/
theorem HasBasis.limsup_eq_ite {v : Filter ι} {p : ι' -> Prop} {s : ι' -> Set ι}
    [Countable (Subtype p)] [Nonempty (Subtype p)] (hv : v.HasBasis p s) (f : ι -> α) :
    limsup f v = if exists (j : Subtype p), s j = ∅ then sInf univ else
      if forall (j : Subtype p), ¬BddAbove (range (fun (i : s j) => f i)) then sInf ∅
      else ⨅ (j : Subtype p), ⨆ (i : s (limsupReparam f s p j)), f i :=
  HasBasis.liminf_eq_ite (α := αᵒᵈ) hv f

end Classical

end ConditionallyCompleteLinearOrder

end Filter

section Order

/--
theorem `GaloisConnection.l_limsup_le` / 定理 `GaloisConnection.l_limsup_le`

English:
theorem GaloisConnection.l_limsup_le
  statement: [ConditionallyCompleteLattice β]
  proof: by
  refine le_limsSup_of_le hlv fun c hc => ?_
  rw [Filter.eventually_map] at hc
  simp_rw [gc _ _] at hc ⊢
  exact limsSup_le_of_le hv_co hc

中文:
定理 GaloisConnection.l_limsup_le
  结论: [条件完备格 β]
  证明: by
  refine le_limsSup_of_le hlv fun c hc => ?_
  rw [Filter.eventually_map] at hc
  simp_rw [gc _ _] at hc ⊢
  exact limsSup_le_of_le hv_co hc

Depends on / 依赖: Filter, Filter.eventually_map, IsCoboundedUnder, eventually_map, f.IsCoboundedUnder, hv_co, isBoundedDefault, le_limsSup_of_le, limsSup_le_of_le, limsup, simp_rw
-/
theorem GaloisConnection.l_limsup_le [ConditionallyCompleteLattice β]
    [ConditionallyCompleteLattice γ] {f : Filter α} {v : α -> β} {l : β -> γ} {u : γ -> β}
    (gc : GaloisConnection l u)
    (hlv : f.IsBoundedUnder (· <= ·) fun x => l (v x) := by isBoundedDefault)
    (hv_co : f.IsCoboundedUnder (· <= ·) v := by isBoundedDefault) :
    l (limsup v f) <= limsup (fun x => l (v x)) f := by
  refine le_limsSup_of_le hlv fun c hc => ?_
  rw [Filter.eventually_map] at hc
  simp_rw [gc _ _] at hc ⊢
  exact limsSup_le_of_le hv_co hc

/--
theorem `OrderIso.limsup_apply` / 定理 `OrderIso.limsup_apply`

English:
theorem OrderIso.limsup_apply
  statement: {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ]
  proof: by
  refine le_antisymm ((OrderIso.to_galoisConnection g).l_limsup_le hgu hu_co) ?_
  rw [← g.symm.symm_apply_apply <| limsup (fun x => g (u x)) f]; rw [g.symm_symm]
  refine g.monotone ?_
  have hf : u = fun i => g.symm (g (u i)) := funext fun i => (g.symm_apply_apply (u i)).symm
  nth_rw 2 [hf]
  

中文:
定理 OrderIso.limsup_apply
  结论: {γ} [条件完备格 β] [条件完备格 γ]
  证明: by
  refine le_antisymm ((OrderIso.to_galoisConnection g).l_limsup_le hgu hu_co) ?_
  rw [← g.symm.symm_apply_apply <| limsup (fun x => g (u x)) f]; rw [g.symm_symm]
  refine g.monotone ?_
  have hf : u = fun i => g.symm (g (u i)) := funext fun i => (g.symm_apply_apply (u i)).symm
  nth_rw 2 [hf]
  

Depends on / 依赖: IsBoundedUnder, IsCoboundedUnder, OrderIso, OrderIso.to_galoisConnection, f.IsBoundedUnder, f.IsCoboundedUnder, g.monotone, g.symm, g.symm.symm_apply_apply, g.symm_symm, hgu_co, hu_co, isBoundedDefault, l_limsup_le, le_antisymm, limsup, monotone, symm_apply_apply, symm_symm, to_galoisConnection
-/
theorem OrderIso.limsup_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ]
    {f : Filter α} {u : α -> β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· <= ·) u := by isBoundedDefault)
    (hu_co : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
    (hgu : f.IsBoundedUnder (· <= ·) fun x => g (u x) := by isBoundedDefault)
    (hgu_co : f.IsCoboundedUnder (· <= ·) fun x => g (u x) := by isBoundedDefault) :
    g (limsup u f) = limsup (fun x => g (u x)) f := by
  refine le_antisymm ((OrderIso.to_galoisConnection g).l_limsup_le hgu hu_co) ?_
  rw [← g.symm.symm_apply_apply <| limsup (fun x => g (u x)) f]; rw [g.symm_symm]
  refine g.monotone ?_
  have hf : u = fun i => g.symm (g (u i)) := funext fun i => (g.symm_apply_apply (u i)).symm
  nth_rw 2 [hf]
  refine (OrderIso.to_galoisConnection g.symm).l_limsup_le ?_ hgu_co
  simp_rw [g.symm_apply_apply]
  exact hu

/--
theorem `OrderIso.liminf_apply` / 定理 `OrderIso.liminf_apply`

English:
theorem OrderIso.liminf_apply
  statement: {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ]
  proof: OrderIso.limsup_apply (β := βᵒᵈ) (γ := γᵒᵈ) g.dual hu hu_co hgu hgu_co

中文:
定理 OrderIso.liminf_apply
  结论: {γ} [条件完备格 β] [条件完备格 γ]
  证明: OrderIso.limsup_apply (β := βᵒᵈ) (γ := γᵒᵈ) g.dual hu hu_co hgu hgu_co

Depends on / 依赖: IsBoundedUnder, IsCoboundedUnder, OrderIso, OrderIso.limsup_apply, f.IsBoundedUnder, f.IsCoboundedUnder, g.dual, hgu_co, hu_co, isBoundedDefault, liminf, limsup_apply
-/
theorem OrderIso.liminf_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ]
    {f : Filter α} {u : α -> β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault)
    (hu_co : f.IsCoboundedUnder (· >= ·) u := by isBoundedDefault)
    (hgu : f.IsBoundedUnder (· >= ·) fun x => g (u x) := by isBoundedDefault)
    (hgu_co : f.IsCoboundedUnder (· >= ·) fun x => g (u x) := by isBoundedDefault) :
    g (liminf u f) = liminf (fun x => g (u x)) f :=
  OrderIso.limsup_apply (β := βᵒᵈ) (γ := γᵒᵈ) g.dual hu hu_co hgu hgu_co

end Order

section MinMax

open Filter

/--
theorem `limsup_max` / 定理 `limsup_max`

English:
theorem limsup_max
  statement: [ConditionallyCompleteLinearOrder β] {f : Filter α} {u v : α -> β}
  proof: by
  have bddmax := IsBoundedUnder.sup h₃ h₄
  have cobddmax := isCoboundedUnder_le_max (v := v) (Or.inl h₁)
  apply le_antisymm
  · refine (limsup_le_iff cobddmax bddmax).2 (fun b hb => ?_)
    have hu := eventually_lt_of_limsup_lt (lt_of_le_of_lt (le_max_left _ _) hb) h₃
    have hv := eventually_

中文:
定理 limsup_max
  结论: [条件完备线性序 β] {f : 滤子 α} {u v : α -> β}
  证明: by
  have bddmax := IsBoundedUnder.sup h₃ h₄
  have cobddmax := isCoboundedUnder_le_max (v := v) (Or.inl h₁)
  apply le_antisymm
  · refine (limsup_le_iff cobddmax bddmax).2 (fun b hb => ?_)
    have hu := eventually_lt_of_limsup_lt (lt_of_le_of_lt (le_max_left _ _) hb) h₃
    have hv := eventually_

Depends on / 依赖: IsBoundedUnder, IsBoundedUnder.sup, IsCoboundedUnder, Or.inl, bddmax, cobddmax, eventually_lt_of_limsup_lt, f.IsBoundedUnder, f.IsCoboundedUnder, isBoundedDefault, isCoboundedUnder_le_max, le_antisymm, limsup, limsup_le_iff, lt_of_le
-/
theorem limsup_max [ConditionallyCompleteLinearOrder β] {f : Filter α} {u v : α -> β}
    (h₁ : f.IsCoboundedUnder (· <= ·) u := by isBoundedDefault)
    (h₂ : f.IsCoboundedUnder (· <= ·) v := by isBoundedDefault)
    (h₃ : f.IsBoundedUnder (· <= ·) u := by isBoundedDefault)
    (h₄ : f.IsBoundedUnder (· <= ·) v := by isBoundedDefault) :
    limsup (fun a => max (u a) (v a)) f = max (limsup u f) (limsup v f) := by
  have bddmax := IsBoundedUnder.sup h₃ h₄
  have cobddmax := isCoboundedUnder_le_max (v := v) (Or.inl h₁)
  apply le_antisymm
  · refine (limsup_le_iff cobddmax bddmax).2 (fun b hb => ?_)
    have hu := eventually_lt_of_limsup_lt (lt_of_le_of_lt (le_max_left _ _) hb) h₃
    have hv := eventually_lt_of_limsup_lt (lt_of_le_of_lt (le_max_right _ _) hb) h₄
    refine mem_of_superset (inter_mem hu hv) (fun _ => by simp)
  · exact max_le (c := limsup (fun a => max (u a) (v a)) f)
      (limsup_le_limsup (Eventually.of_forall (fun a : α => le_max_left (u a) (v a))) h₁ bddmax)
      (limsup_le_limsup (Eventually.of_forall (fun a : α => le_max_right (u a) (v a))) h₂ bddmax)

/--
theorem `liminf_min` / 定理 `liminf_min`

English:
theorem liminf_min
  statement: [ConditionallyCompleteLinearOrder β] {f : Filter α} {u v : α -> β}
  proof: limsup_max (β := βᵒᵈ) h₁ h₂ h₃ h₄

中文:
定理 liminf_min
  结论: [条件完备线性序 β] {f : 滤子 α} {u v : α -> β}
  证明: limsup_max (β := βᵒᵈ) h₁ h₂ h₃ h₄

Depends on / 依赖: IsBoundedUnder, IsCoboundedUnder, f.IsBoundedUnder, f.IsCoboundedUnder, isBoundedDefault, liminf, limsup_max
-/
theorem liminf_min [ConditionallyCompleteLinearOrder β] {f : Filter α} {u v : α -> β}
    (h₁ : f.IsCoboundedUnder (· >= ·) u := by isBoundedDefault)
    (h₂ : f.IsCoboundedUnder (· >= ·) v := by isBoundedDefault)
    (h₃ : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault)
    (h₄ : f.IsBoundedUnder (· >= ·) v := by isBoundedDefault) :
    liminf (fun a => min (u a) (v a)) f = min (liminf u f) (liminf v f) :=
  limsup_max (β := βᵒᵈ) h₁ h₂ h₃ h₄

open Finset

/--
theorem `limsup_finset_sup'` / 定理 `limsup_finset_sup'`

English:
theorem limsup_finset_sup'
  statement: [ConditionallyCompleteLinearOrder β] {f : Filter α}
  proof: by
  have bddsup := isBoundedUnder_le_finset_sup' hs h₂
  apply le_antisymm
  · have h₃ : exists i in s, f.IsCoboundedUnder (· <= ·) (F i) := by
      rcases hs with ⟨i, i_s⟩
      use i, i_s
      exact h₁ i i_s
    have cobddsup := isCoboundedUnder_le_finset_sup' hs h₃
    refine (limsup_le_iff co

中文:
定理 limsup_finset_sup'
  结论: [条件完备线性序 β] {f : 滤子 α}
  证明: by
  have bddsup := isBoundedUnder_le_finset_sup' hs h₂
  apply le_antisymm
  · have h₃ : exists i in s, f.IsCoboundedUnder (· <= ·) (F i) := by
      rcases hs with ⟨i, i_s⟩
      use i, i_s
      exact h₁ i i_s
    have cobddsup := isCoboundedUnder_le_finset_sup' hs h₃
    refine (limsup_le_iff co

Depends on / 依赖: IsBoundedUnder, IsCoboundedUnder, bddsup, cobdds, cobddsup, f.IsBoundedUnder, f.IsCoboundedUnder, isBoundedDefault, isBoundedUnder_le_finset_sup, isCoboundedUnder_le_finset_sup, le_antisymm, limsup, limsup_le_iff
-/
theorem limsup_finset_sup' [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {F : ι -> α -> β} {s : Finset ι} (hs : s.Nonempty)
    (h₁ : forall i in s, f.IsCoboundedUnder (· <= ·) (F i) := by exact fun _ _ => by isBoundedDefault)
    (h₂ : forall i in s, f.IsBoundedUnder (· <= ·) (F i) := by exact fun _ _ => by isBoundedDefault) :
    limsup (fun a => sup' s hs (fun i => F i a)) f = sup' s hs (fun i => limsup (F i) f) := by
  have bddsup := isBoundedUnder_le_finset_sup' hs h₂
  apply le_antisymm
  · have h₃ : exists i in s, f.IsCoboundedUnder (· <= ·) (F i) := by
      rcases hs with ⟨i, i_s⟩
      use i, i_s
      exact h₁ i i_s
    have cobddsup := isCoboundedUnder_le_finset_sup' hs h₃
    refine (limsup_le_iff cobddsup bddsup).2 (fun b hb => ?_)
    simp only [gt_iff_lt, sup'_lt_iff, eventually_all_finset] at hb ⊢
    exact fun i i_s => eventually_lt_of_limsup_lt (hb i i_s) (h₂ i i_s)
  · apply Finset.sup'_le hs (fun i => limsup (F i) f)
    refine fun i i_s => limsup_le_limsup (Eventually.of_forall (fun a => ?_)) (h₁ i i_s) bddsup
    simp only [le_sup'_iff]
    use i, i_s

/--
theorem `limsup_finset_sup` / 定理 `limsup_finset_sup`

English:
theorem limsup_finset_sup
  statement: [ConditionallyCompleteLinearOrder β] [OrderBot β] {f : Filter α}
  proof: by
  rcases eq_or_neBot f with (rfl | _)
  · simp [limsup_eq, csInf_univ]
  rcases Finset.eq_empty_or_nonempty s with (rfl | s_nemp)
  · simp only [sup_empty, limsup_const]
  rw [← Finset.sup'_eq_sup s_nemp fun i => limsup (F i) f]; rw [← limsup_finset_sup' s_nemp h₁ h₂]
  congr
  ext a
  exact Eq.s

中文:
定理 limsup_finset_sup
  结论: [条件完备线性序 β] [有底序 β] {f : 滤子 α}
  证明: by
  rcases eq_or_neBot f with (rfl | _)
  · simp [limsup_eq, csInf_univ]
  rcases Finset.eq_empty_or_nonempty s with (rfl | s_nemp)
  · simp only [sup_empty, limsup_const]
  rw [← Finset.sup'_eq_sup s_nemp fun i => limsup (F i) f]; rw [← limsup_finset_sup' s_nemp h₁ h₂]
  congr
  ext a
  exact Eq.s

Depends on / 依赖: Finset, Finset.eq_empty_or_nonempty, Finset.sup, IsBoundedUnder, _eq_sup, csInf_univ, eq_empty_or_nonempty, eq_or_neBot, f.IsBoundedUnder, isBoundedDefault, limsup, limsup_const, limsup_eq, limsup_finset_sup, s_nemp, sup_empty
-/
theorem limsup_finset_sup [ConditionallyCompleteLinearOrder β] [OrderBot β] {f : Filter α}
    {F : ι -> α -> β} {s : Finset ι}
    (h₁ : forall i in s, f.IsCoboundedUnder (· <= ·) (F i) := by exact fun _ _ => by isBoundedDefault)
    (h₂ : forall i in s, f.IsBoundedUnder (· <= ·) (F i) := by exact fun _ _ => by isBoundedDefault) :
    limsup (fun a => sup s (fun i => F i a)) f = sup s (fun i => limsup (F i) f) := by
  rcases eq_or_neBot f with (rfl | _)
  · simp [limsup_eq, csInf_univ]
  rcases Finset.eq_empty_or_nonempty s with (rfl | s_nemp)
  · simp only [sup_empty, limsup_const]
  rw [← Finset.sup'_eq_sup s_nemp fun i => limsup (F i) f]; rw [← limsup_finset_sup' s_nemp h₁ h₂]
  congr
  ext a
  exact Eq.symm (Finset.sup'_eq_sup s_nemp (fun i => F i a))

/--
theorem `liminf_finset_inf'` / 定理 `liminf_finset_inf'`

English:
theorem liminf_finset_inf'
  statement: [ConditionallyCompleteLinearOrder β] {f : Filter α}
  proof: limsup_finset_sup' (β := βᵒᵈ) hs h₁ h₂

中文:
定理 liminf_finset_inf'
  结论: [条件完备线性序 β] {f : 滤子 α}
  证明: limsup_finset_sup' (β := βᵒᵈ) hs h₁ h₂

Depends on / 依赖: IsBoundedUnder, f.IsBoundedUnder, isBoundedDefault, liminf, limsup_finset_sup
-/
theorem liminf_finset_inf' [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {F : ι -> α -> β} {s : Finset ι} (hs : s.Nonempty)
    (h₁ : forall i in s, f.IsCoboundedUnder (· >= ·) (F i) := by exact fun _ _ => by isBoundedDefault)
    (h₂ : forall i in s, f.IsBoundedUnder (· >= ·) (F i) := by exact fun _ _ => by isBoundedDefault) :
    liminf (fun a => inf' s hs (fun i => F i a)) f = inf' s hs (fun i => liminf (F i) f) :=
  limsup_finset_sup' (β := βᵒᵈ) hs h₁ h₂

/--
theorem `liminf_finset_inf` / 定理 `liminf_finset_inf`

English:
theorem liminf_finset_inf
  statement: [ConditionallyCompleteLinearOrder β] [OrderTop β] {f : Filter α}
  proof: limsup_finset_sup (β := βᵒᵈ) h₁ h₂

中文:
定理 liminf_finset_inf
  结论: [条件完备线性序 β] [有顶序 β] {f : 滤子 α}
  证明: limsup_finset_sup (β := βᵒᵈ) h₁ h₂

Depends on / 依赖: IsBoundedUnder, f.IsBoundedUnder, isBoundedDefault, liminf, limsup_finset_sup
-/
theorem liminf_finset_inf [ConditionallyCompleteLinearOrder β] [OrderTop β] {f : Filter α}
    {F : ι -> α -> β} {s : Finset ι}
    (h₁ : forall i in s, f.IsCoboundedUnder (· >= ·) (F i) := by exact fun _ _ => by isBoundedDefault)
    (h₂ : forall i in s, f.IsBoundedUnder (· >= ·) (F i) := by exact fun _ _ => by isBoundedDefault) :
    liminf (fun a => inf s (fun i => F i a)) f = inf s (fun i => liminf (F i) f) :=
  limsup_finset_sup (β := βᵒᵈ) h₁ h₂

end MinMax
