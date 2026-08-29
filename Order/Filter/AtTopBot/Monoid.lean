/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# Convergence to ±infinity in ordered commutative monoids
-/

public section

variable {α M : Type*}

namespace Filter

section OrderedCommMonoid

variable [CommMonoid M] [Preorder M] [IsOrderedMonoid M] {l : Filter α} {f g : α -> M}

@[to_additive]
/--
theorem `Tendsto.one_eventuallyLE_mul_atTop` / 定理 `Tendsto.one_eventuallyLE_mul_atTop`

English:
theorem Tendsto.one_eventuallyLE_mul_atTop
  given: (hf : 1 <=ᶠ[l] f) (hg : Tendsto g l atTop)
  proof: tendsto_atTop_mono' l (hf.mono fun _ => le_mul_of_one_le_left') hg

@[to_additive]

中文:
定理 Tendsto.one_eventuallyLE_mul_atTop
  条件: (hf : 1 <=ᶠ[l] f) (hg : Tendsto g l atTop)
  证明: tendsto_atTop_mono' l (hf.mono fun _ => le_mul_of_one_le_left') hg

@[to_additive]

Depends on / 依赖: hf.mono, le_mul_of_one_le_left, tendsto_atTop_mono
-/
theorem Tendsto.one_eventuallyLE_mul_atTop (hf : 1 <=ᶠ[l] f) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  tendsto_atTop_mono' l (hf.mono fun _ => le_mul_of_one_le_left') hg

@[to_additive]
/--
theorem `Tendsto.eventuallyLE_one_mul_atBot` / 定理 `Tendsto.eventuallyLE_one_mul_atBot`

English:
theorem Tendsto.eventuallyLE_one_mul_atBot
  given: (hf : f <=ᶠ[l] 1) (hg : Tendsto g l atBot)
  proof: hg.one_eventuallyLE_mul_atTop (M := Mᵒᵈ) hf

@[to_additive]

中文:
定理 Tendsto.eventuallyLE_one_mul_atBot
  条件: (hf : f <=ᶠ[l] 1) (hg : Tendsto g l atBot)
  证明: hg.one_eventuallyLE_mul_atTop (M := Mᵒᵈ) hf

@[to_additive]

Depends on / 依赖: hg.one_eventuallyLE_mul_atTop, one_eventuallyLE_mul_atTop
-/
theorem Tendsto.eventuallyLE_one_mul_atBot (hf : f <=ᶠ[l] 1) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  hg.one_eventuallyLE_mul_atTop (M := Mᵒᵈ) hf

@[to_additive]
/--
theorem `Tendsto.one_le_mul_atTop` / 定理 `Tendsto.one_le_mul_atTop`

English:
theorem Tendsto.one_le_mul_atTop
  given: (hf : forall x, 1 <= f x) (hg : Tendsto g l atTop)
  proof: hg.one_eventuallyLE_mul_atTop (.of_forall hf)

@[to_additive]

中文:
定理 Tendsto.one_le_mul_atTop
  条件: (hf : 对任意 x, 1 <= f x) (hg : Tendsto g l atTop)
  证明: hg.one_eventuallyLE_mul_atTop (.of_forall hf)

@[to_additive]

Depends on / 依赖: hg.one_eventuallyLE_mul_atTop, of_forall, one_eventuallyLE_mul_atTop
-/
theorem Tendsto.one_le_mul_atTop (hf : forall x, 1 <= f x) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  hg.one_eventuallyLE_mul_atTop (.of_forall hf)

@[to_additive]
/--
theorem `Tendsto.le_one_mul_atBot` / 定理 `Tendsto.le_one_mul_atBot`

English:
theorem Tendsto.le_one_mul_atBot
  given: (hf : forall x, f x <= 1) (hg : Tendsto g l atBot)
  proof: hg.eventuallyLE_one_mul_atBot (.of_forall hf)

@[to_additive]

中文:
定理 Tendsto.le_one_mul_atBot
  条件: (hf : 对任意 x, f x <= 1) (hg : Tendsto g l atBot)
  证明: hg.eventuallyLE_one_mul_atBot (.of_forall hf)

@[to_additive]

Depends on / 依赖: eventuallyLE_one_mul_atBot, hg.eventuallyLE_one_mul_atBot, of_forall
-/
theorem Tendsto.le_one_mul_atBot (hf : forall x, f x <= 1) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  hg.eventuallyLE_one_mul_atBot (.of_forall hf)

@[to_additive]
/--
theorem `Tendsto.atTop_mul_one_eventuallyLE` / 定理 `Tendsto.atTop_mul_one_eventuallyLE`

English:
theorem Tendsto.atTop_mul_one_eventuallyLE
  given: (hf : Tendsto f l atTop) (hg : 1 <=ᶠ[l] g)
  proof: tendsto_atTop_mono' l (hg.mono fun _ => le_mul_of_one_le_right') hf

@[to_additive]

中文:
定理 Tendsto.atTop_mul_one_eventuallyLE
  条件: (hf : Tendsto f l atTop) (hg : 1 <=ᶠ[l] g)
  证明: tendsto_atTop_mono' l (hg.mono fun _ => le_mul_of_one_le_right') hf

@[to_additive]

Depends on / 依赖: hg.mono, le_mul_of_one_le_right, tendsto_atTop_mono
-/
theorem Tendsto.atTop_mul_one_eventuallyLE (hf : Tendsto f l atTop) (hg : 1 <=ᶠ[l] g) :
    Tendsto (fun x => f x * g x) l atTop :=
  tendsto_atTop_mono' l (hg.mono fun _ => le_mul_of_one_le_right') hf

@[to_additive]
/--
theorem `Tendsto.atBot_mul_eventuallyLE_one` / 定理 `Tendsto.atBot_mul_eventuallyLE_one`

English:
theorem Tendsto.atBot_mul_eventuallyLE_one
  given: (hf : Tendsto f l atBot) (hg : g <=ᶠ[l] 1)
  proof: hf.atTop_mul_one_eventuallyLE (M := Mᵒᵈ) hg

@[to_additive]

中文:
定理 Tendsto.atBot_mul_eventuallyLE_one
  条件: (hf : Tendsto f l atBot) (hg : g <=ᶠ[l] 1)
  证明: hf.atTop_mul_one_eventuallyLE (M := Mᵒᵈ) hg

@[to_additive]

Depends on / 依赖: atTop_mul_one_eventuallyLE, hf.atTop_mul_one_eventuallyLE
-/
theorem Tendsto.atBot_mul_eventuallyLE_one (hf : Tendsto f l atBot) (hg : g <=ᶠ[l] 1) :
    Tendsto (fun x => f x * g x) l atBot :=
  hf.atTop_mul_one_eventuallyLE (M := Mᵒᵈ) hg

@[to_additive]
/--
theorem `Tendsto.atTop_mul_one_le` / 定理 `Tendsto.atTop_mul_one_le`

English:
theorem Tendsto.atTop_mul_one_le
  given: (hf : Tendsto f l atTop) (hg : forall x, 1 <= g x)
  proof: hf.atTop_mul_one_eventuallyLE .of_forall hg

@[to_additive]

中文:
定理 Tendsto.atTop_mul_one_le
  条件: (hf : Tendsto f l atTop) (hg : 对任意 x, 1 <= g x)
  证明: hf.atTop_mul_one_eventuallyLE .of_forall hg

@[to_additive]

Depends on / 依赖: atTop_mul_one_eventuallyLE, hf.atTop_mul_one_eventuallyLE, of_forall
-/
theorem Tendsto.atTop_mul_one_le (hf : Tendsto f l atTop) (hg : forall x, 1 <= g x) :
    Tendsto (fun x => f x * g x) l atTop :=
hf.atTop_mul_one_eventuallyLE .of_forall hg

@[to_additive]
/--
theorem `Tendsto.atBot_mul_le_one` / 定理 `Tendsto.atBot_mul_le_one`

English:
theorem Tendsto.atBot_mul_le_one
  given: (hf : Tendsto f l atBot) (hg : forall x, g x <= 1)
  proof: hf.atBot_mul_eventuallyLE_one (.of_forall hg)

中文:
定理 Tendsto.atBot_mul_le_one
  条件: (hf : Tendsto f l atBot) (hg : 对任意 x, g x <= 1)
  证明: hf.atBot_mul_eventuallyLE_one (.of_forall hg)

Depends on / 依赖: atBot_mul_eventuallyLE_one, hf.atBot_mul_eventuallyLE_one, of_forall
-/
theorem Tendsto.atBot_mul_le_one (hf : Tendsto f l atBot) (hg : forall x, g x <= 1) :
    Tendsto (fun x => f x * g x) l atBot :=
  hf.atBot_mul_eventuallyLE_one (.of_forall hg)

/-- In an ordered multiplicative monoid, if `f` and `g` tend to `+∞`, then so does `f * g`.

Earlier, this name was used for a similar lemma about semirings,
which is now called `Filter.Tendsto.atTop_mul_atTop₀`. -/
@[to_additive]
/--
theorem `Tendsto.atTop_mul_atTop` / 定理 `Tendsto.atTop_mul_atTop`

English:
theorem Tendsto.atTop_mul_atTop
  given: (hf : Tendsto f l atTop) (hg : Tendsto g l atTop)
  proof: hf.atTop_mul_one_eventuallyLE hg.eventually_ge_atTop 1

中文:
定理 Tendsto.atTop_mul_atTop
  条件: (hf : Tendsto f l atTop) (hg : Tendsto g l atTop)
  证明: hf.atTop_mul_one_eventuallyLE hg.eventually_ge_atTop 1

Depends on / 依赖: atTop_mul_one_eventuallyLE, eventually_ge_atTop, hf.atTop_mul_one_eventuallyLE, hg.eventually_ge_atTop
-/
theorem Tendsto.atTop_mul_atTop (hf : Tendsto f l atTop) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
hf.atTop_mul_one_eventuallyLE hg.eventually_ge_atTop 1

/-- In an ordered multiplicative monoid, if `f` and `g` tend to `-∞`, then so does `f * g`.

Earlier, this name was used for a similar lemma about rings (with conclusion `f * g → +∞`),
which is now called `Filter.Tendsto.atBot_mul_atBot₀`. -/
@[to_additive]
/--
theorem `Tendsto.atBot_mul_atBot` / 定理 `Tendsto.atBot_mul_atBot`

English:
theorem Tendsto.atBot_mul_atBot
  given: (hf : Tendsto f l atBot) (hg : Tendsto g l atBot)
  proof: hf.atTop_mul_atTop (M := Mᵒᵈ) hg

@[to_additive nsmul_atTop]

中文:
定理 Tendsto.atBot_mul_atBot
  条件: (hf : Tendsto f l atBot) (hg : Tendsto g l atBot)
  证明: hf.atTop_mul_atTop (M := Mᵒᵈ) hg

@[to_additive nsmul_atTop]

Depends on / 依赖: atTop_mul_atTop, hf.atTop_mul_atTop
-/
theorem Tendsto.atBot_mul_atBot (hf : Tendsto f l atBot) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  hf.atTop_mul_atTop (M := Mᵒᵈ) hg

@[to_additive nsmul_atTop]
/--
theorem `Tendsto.atTop_pow` / 定理 `Tendsto.atTop_pow`

English:
theorem Tendsto.atTop_pow
  given: (hf : Tendsto f l atTop) {n : Nat} (hn : 0 < n)
  proof: by
  refine tendsto_atTop_mono' _ ((hf.eventually_ge_atTop 1).mono fun x hx => ?_) hf
  simpa only [pow_one] using pow_le_pow_right' hx hn

@[to_additive nsmul_atBot]

中文:
定理 Tendsto.atTop_pow
  条件: (hf : Tendsto f l atTop) {n : 自然数} (hn : 0 < n)
  证明: by
  refine tendsto_atTop_mono' _ ((hf.eventually_ge_atTop 1).mono fun x hx => ?_) hf
  simpa only [pow_one] using pow_le_pow_right' hx hn

@[to_additive nsmul_atBot]

Depends on / 依赖: eventually_ge_atTop, hf.eventually_ge_atTop, pow_le_pow_right, pow_one, tendsto_atTop_mono
-/
theorem Tendsto.atTop_pow (hf : Tendsto f l atTop) {n : Nat} (hn : 0 < n) :
    Tendsto (fun x => f x ^ n) l atTop := by
  refine tendsto_atTop_mono' _ ((hf.eventually_ge_atTop 1).mono fun x hx => ?_) hf
  simpa only [pow_one] using pow_le_pow_right' hx hn

@[to_additive nsmul_atBot]
/--
theorem `Tendsto.atBot_pow` / 定理 `Tendsto.atBot_pow`

English:
theorem Tendsto.atBot_pow
  given: (hf : Tendsto f l atBot) {n : Nat} (hn : 0 < n)
  proof: Tendsto.atTop_pow (M := Mᵒᵈ) hf hn

中文:
定理 Tendsto.atBot_pow
  条件: (hf : Tendsto f l atBot) {n : 自然数} (hn : 0 < n)
  证明: Tendsto.atTop_pow (M := Mᵒᵈ) hf hn

Depends on / 依赖: Tendsto, Tendsto.atTop_pow, atTop_pow
-/
theorem Tendsto.atBot_pow (hf : Tendsto f l atBot) {n : Nat} (hn : 0 < n) :
    Tendsto (fun x => f x ^ n) l atBot :=
  Tendsto.atTop_pow (M := Mᵒᵈ) hf hn

end OrderedCommMonoid

section OrderedCancelCommMonoid

variable [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M] {l : Filter α} {f g : α -> M}

/-- In an ordered cancellative multiplicative monoid, if `C * f x → +∞`, then `f x → +∞`.

Earlier, this name was used for a similar lemma about ordered rings,
which is now called `Filter.Tendsto.atTop_of_const_mul₀`. -/
@[to_additive]
/--
theorem `Tendsto.atTop_of_const_mul` / 定理 `Tendsto.atTop_of_const_mul`

English:
theorem Tendsto.atTop_of_const_mul
  given: (C : M) (hf : Tendsto (C * f ·) l atTop)
  statement: Tendsto f l atTop
  proof: tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (C * b)).mono fun _ => le_of_mul_le_mul_left'

@[to_additive]

中文:
定理 Tendsto.atTop_of_const_mul
  条件: (C : M) (hf : Tendsto (C * f ·) l atTop)
  结论: Tendsto f l atTop
  证明: tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (C * b)).mono fun _ => le_of_mul_le_mul_left'

@[to_additive]

Depends on / 依赖: le_of_mul_le_mul_left, tendsto_atTop
-/
theorem Tendsto.atTop_of_const_mul (C : M) (hf : Tendsto (C * f ·) l atTop) : Tendsto f l atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (C * b)).mono fun _ => le_of_mul_le_mul_left'

@[to_additive]
/--
theorem `Tendsto.atBot_of_const_mul` / 定理 `Tendsto.atBot_of_const_mul`

English:
theorem Tendsto.atBot_of_const_mul
  given: (C : M) (hf : Tendsto (C * f ·) l atBot)
  statement: Tendsto f l atBot
  proof: hf.atTop_of_const_mul (M := Mᵒᵈ)

中文:
定理 Tendsto.atBot_of_const_mul
  条件: (C : M) (hf : Tendsto (C * f ·) l atBot)
  结论: Tendsto f l atBot
  证明: hf.atTop_of_const_mul (M := Mᵒᵈ)

Depends on / 依赖: atTop_of_const_mul, hf.atTop_of_const_mul
-/
theorem Tendsto.atBot_of_const_mul (C : M) (hf : Tendsto (C * f ·) l atBot) : Tendsto f l atBot :=
  hf.atTop_of_const_mul (M := Mᵒᵈ)

/-- In an ordered cancellative multiplicative monoid, if `f x * C → +∞`, then `f x → +∞`.

Earlier, this name was used for a similar lemma about ordered rings,
which is now called `Filter.Tendsto.atTop_of_mul_const₀`. -/
@[to_additive]
/--
theorem `Tendsto.atTop_of_mul_const` / 定理 `Tendsto.atTop_of_mul_const`

English:
theorem Tendsto.atTop_of_mul_const
  given: (C : M) (hf : Tendsto (f · * C) l atTop)
  statement: Tendsto f l atTop
  proof: tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (b * C)).mono fun _ => le_of_mul_le_mul_right'

@[to_additive]

中文:
定理 Tendsto.atTop_of_mul_const
  条件: (C : M) (hf : Tendsto (f · * C) l atTop)
  结论: Tendsto f l atTop
  证明: tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (b * C)).mono fun _ => le_of_mul_le_mul_right'

@[to_additive]

Depends on / 依赖: le_of_mul_le_mul_right, tendsto_atTop
-/
theorem Tendsto.atTop_of_mul_const (C : M) (hf : Tendsto (f · * C) l atTop) : Tendsto f l atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (b * C)).mono fun _ => le_of_mul_le_mul_right'

@[to_additive]
/--
theorem `Tendsto.atBot_of_mul_const` / 定理 `Tendsto.atBot_of_mul_const`

English:
theorem Tendsto.atBot_of_mul_const
  given: (C : M) (hf : Tendsto (f · * C) l atBot)
  statement: Tendsto f l atBot
  proof: hf.atTop_of_mul_const (M := Mᵒᵈ)

中文:
定理 Tendsto.atBot_of_mul_const
  条件: (C : M) (hf : Tendsto (f · * C) l atBot)
  结论: Tendsto f l atBot
  证明: hf.atTop_of_mul_const (M := Mᵒᵈ)

Depends on / 依赖: atTop_of_mul_const, hf.atTop_of_mul_const
-/
theorem Tendsto.atBot_of_mul_const (C : M) (hf : Tendsto (f · * C) l atBot) : Tendsto f l atBot :=
  hf.atTop_of_mul_const (M := Mᵒᵈ)

/-- If `f` is eventually bounded from above along `l` and `f * g` tends to `+∞`,
then `g` tends to `+∞`. -/
@[to_additive /-- If `f` is eventually bounded from above along `l` and `f + g` tends to `+∞`,
then `g` tends to `+∞`. -/]
/--
theorem `Tendsto.atTop_of_isBoundedUnder_le_mul` / 定理 `Tendsto.atTop_of_isBoundedUnder_le_mul`

English:
theorem Tendsto.atTop_of_isBoundedUnder_le_mul
  statement: (hf : IsBoundedUnder (· <= ·) l f)
  proof: by
  obtain ⟨C, hC⟩ := hf
refine .atTop_of_const_mul C tendsto_atTop_mono' l ?_ hfg
  exact (eventually_map.mp hC).mono fun _ _ => by dsimp; gcongr

@[to_additive]

中文:
定理 Tendsto.atTop_of_isBoundedUnder_le_mul
  结论: (hf : IsBoundedUnder (· <= ·) l f)
  证明: by
  obtain ⟨C, hC⟩ := hf
refine .atTop_of_const_mul C tendsto_atTop_mono' l ?_ hfg
  exact (eventually_map.mp hC).mono fun _ _ => by dsimp; gcongr

@[to_additive]

Depends on / 依赖: atTop_of_const_mul, eventually_map, eventually_map.mp, tendsto_atTop_mono
-/
theorem Tendsto.atTop_of_isBoundedUnder_le_mul (hf : IsBoundedUnder (· <= ·) l f)
    (hfg : Tendsto (fun x => f x * g x) l atTop) : Tendsto g l atTop := by
  obtain ⟨C, hC⟩ := hf
refine .atTop_of_const_mul C tendsto_atTop_mono' l ?_ hfg
  exact (eventually_map.mp hC).mono fun _ _ => by dsimp; gcongr

@[to_additive]
/--
theorem `Tendsto.atBot_of_isBoundedUnder_ge_mul` / 定理 `Tendsto.atBot_of_isBoundedUnder_ge_mul`

English:
theorem Tendsto.atBot_of_isBoundedUnder_ge_mul
  statement: (hf : IsBoundedUnder (· >= ·) l f)
  proof: h.atTop_of_isBoundedUnder_le_mul (M := Mᵒᵈ) hf

@[to_additive]

中文:
定理 Tendsto.atBot_of_isBoundedUnder_ge_mul
  结论: (hf : IsBoundedUnder (· >= ·) l f)
  证明: h.atTop_of_isBoundedUnder_le_mul (M := Mᵒᵈ) hf

@[to_additive]

Depends on / 依赖: atTop_of_isBoundedUnder_le_mul, h.atTop_of_isBoundedUnder_le_mul
-/
theorem Tendsto.atBot_of_isBoundedUnder_ge_mul (hf : IsBoundedUnder (· >= ·) l f)
    (h : Tendsto (fun x => f x * g x) l atBot) : Tendsto g l atBot :=
  h.atTop_of_isBoundedUnder_le_mul (M := Mᵒᵈ) hf

@[to_additive]
/--
theorem `Tendsto.atTop_of_le_const_mul` / 定理 `Tendsto.atTop_of_le_const_mul`

English:
theorem Tendsto.atTop_of_le_const_mul
  statement: (hf : exists C, forall x, f x <= C)
  proof: hfg.atTop_of_isBoundedUnder_le_mul hf.imp fun _C hC => eventually_map.mpr .of_forall hC

@[to_additive]

中文:
定理 Tendsto.atTop_of_le_const_mul
  结论: (hf : 存在 C, 对任意 x, f x <= C)
  证明: hfg.atTop_of_isBoundedUnder_le_mul hf.imp fun _C hC => eventually_map.mpr .of_forall hC

@[to_additive]

Depends on / 依赖: atTop_of_isBoundedUnder_le_mul, eventually_map, eventually_map.mpr, hf.imp, hfg.atTop_of_isBoundedUnder_le_mul, of_forall
-/
theorem Tendsto.atTop_of_le_const_mul (hf : exists C, forall x, f x <= C)
    (hfg : Tendsto (fun x => f x * g x) l atTop) : Tendsto g l atTop :=
hfg.atTop_of_isBoundedUnder_le_mul hf.imp fun _C hC => eventually_map.mpr .of_forall hC

@[to_additive]
/--
theorem `Tendsto.atBot_of_const_le_mul` / 定理 `Tendsto.atBot_of_const_le_mul`

English:
theorem Tendsto.atBot_of_const_le_mul
  statement: (hf : exists C, forall x, C <= f x)
  proof: Tendsto.atTop_of_le_const_mul (M := Mᵒᵈ) hf hfg

@[to_additive]

中文:
定理 Tendsto.atBot_of_const_le_mul
  结论: (hf : 存在 C, 对任意 x, C <= f x)
  证明: Tendsto.atTop_of_le_const_mul (M := Mᵒᵈ) hf hfg

@[to_additive]

Depends on / 依赖: Tendsto, Tendsto.atTop_of_le_const_mul, atTop_of_le_const_mul
-/
theorem Tendsto.atBot_of_const_le_mul (hf : exists C, forall x, C <= f x)
    (hfg : Tendsto (fun x => f x * g x) l atBot) : Tendsto g l atBot :=
  Tendsto.atTop_of_le_const_mul (M := Mᵒᵈ) hf hfg

@[to_additive]
/--
theorem `Tendsto.atTop_of_mul_isBoundedUnder_le` / 定理 `Tendsto.atTop_of_mul_isBoundedUnder_le`

English:
theorem Tendsto.atTop_of_mul_isBoundedUnder_le
  statement: (hg : IsBoundedUnder (· <= ·) l g)
  proof: by
  obtain ⟨C, hC⟩ := hg
refine .atTop_of_mul_const C tendsto_atTop_mono' l ?_ h
  exact (eventually_map.mp hC).mono fun _ _ => by dsimp; gcongr

@[to_additive]

中文:
定理 Tendsto.atTop_of_mul_isBoundedUnder_le
  结论: (hg : IsBoundedUnder (· <= ·) l g)
  证明: by
  obtain ⟨C, hC⟩ := hg
refine .atTop_of_mul_const C tendsto_atTop_mono' l ?_ h
  exact (eventually_map.mp hC).mono fun _ _ => by dsimp; gcongr

@[to_additive]

Depends on / 依赖: atTop_of_mul_const, eventually_map, eventually_map.mp, tendsto_atTop_mono
-/
theorem Tendsto.atTop_of_mul_isBoundedUnder_le (hg : IsBoundedUnder (· <= ·) l g)
    (h : Tendsto (fun x => f x * g x) l atTop) : Tendsto f l atTop := by
  obtain ⟨C, hC⟩ := hg
refine .atTop_of_mul_const C tendsto_atTop_mono' l ?_ h
  exact (eventually_map.mp hC).mono fun _ _ => by dsimp; gcongr

@[to_additive]
/--
theorem `Tendsto.atBot_of_mul_isBoundedUnder_ge` / 定理 `Tendsto.atBot_of_mul_isBoundedUnder_ge`

English:
theorem Tendsto.atBot_of_mul_isBoundedUnder_ge
  statement: (hg : IsBoundedUnder (· >= ·) l g)
  proof: h.atTop_of_mul_isBoundedUnder_le (M := Mᵒᵈ) hg

@[to_additive]

中文:
定理 Tendsto.atBot_of_mul_isBoundedUnder_ge
  结论: (hg : IsBoundedUnder (· >= ·) l g)
  证明: h.atTop_of_mul_isBoundedUnder_le (M := Mᵒᵈ) hg

@[to_additive]

Depends on / 依赖: atTop_of_mul_isBoundedUnder_le, h.atTop_of_mul_isBoundedUnder_le
-/
theorem Tendsto.atBot_of_mul_isBoundedUnder_ge (hg : IsBoundedUnder (· >= ·) l g)
    (h : Tendsto (fun x => f x * g x) l atBot) : Tendsto f l atBot :=
  h.atTop_of_mul_isBoundedUnder_le (M := Mᵒᵈ) hg

@[to_additive]
/--
theorem `Tendsto.atTop_of_mul_le_const` / 定理 `Tendsto.atTop_of_mul_le_const`

English:
theorem Tendsto.atTop_of_mul_le_const
  statement: (hg : exists C, forall x, g x <= C)
  proof: hfg.atTop_of_mul_isBoundedUnder_le hg.imp fun _C hC => eventually_map.mpr .of_forall hC

@[to_additive]

中文:
定理 Tendsto.atTop_of_mul_le_const
  结论: (hg : 存在 C, 对任意 x, g x <= C)
  证明: hfg.atTop_of_mul_isBoundedUnder_le hg.imp fun _C hC => eventually_map.mpr .of_forall hC

@[to_additive]

Depends on / 依赖: atTop_of_mul_isBoundedUnder_le, eventually_map, eventually_map.mpr, hfg.atTop_of_mul_isBoundedUnder_le, hg.imp, of_forall
-/
theorem Tendsto.atTop_of_mul_le_const (hg : exists C, forall x, g x <= C)
    (hfg : Tendsto (fun x => f x * g x) l atTop) : Tendsto f l atTop :=
hfg.atTop_of_mul_isBoundedUnder_le hg.imp fun _C hC => eventually_map.mpr .of_forall hC

@[to_additive]
/--
theorem `Tendsto.atBot_of_mul_const_le` / 定理 `Tendsto.atBot_of_mul_const_le`

English:
theorem Tendsto.atBot_of_mul_const_le
  statement: (hg : exists C, forall x, C <= g x)
  proof: Tendsto.atTop_of_mul_le_const (M := Mᵒᵈ) hg hfg

中文:
定理 Tendsto.atBot_of_mul_const_le
  结论: (hg : 存在 C, 对任意 x, C <= g x)
  证明: Tendsto.atTop_of_mul_le_const (M := Mᵒᵈ) hg hfg

Depends on / 依赖: Tendsto, Tendsto.atTop_of_mul_le_const, atTop_of_mul_le_const
-/
theorem Tendsto.atBot_of_mul_const_le (hg : exists C, forall x, C <= g x)
    (hfg : Tendsto (fun x => f x * g x) l atBot) : Tendsto f l atBot :=
  Tendsto.atTop_of_mul_le_const (M := Mᵒᵈ) hg hfg

end OrderedCancelCommMonoid

end Filter
