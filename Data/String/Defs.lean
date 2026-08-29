/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Keeley Hoek, Floris van Doorn, Chris Bailey
-/
module

public import Mathlib.Init
/-!
# Definitions for `String`

This file defines a bunch of functions for the `String` datatype.
-/

@[expose] public section

/--
Definition of `Char.isAscii` / `Char.isAscii` 的定义

English:
definition Char.isAscii
  signature: (c : Char)
  body: c.toNat < 0x80

中文:
定义 Char.isAscii
  签名: (c : Char)
  定义体: c.toNat < 0x80

Depends on / 依赖: c.toNat
-/
def Char.isAscii (c : Char) : Bool := c.toNat < 0x80

namespace String

/--
Definition of `leftpad` / `leftpad` 的定义

English:
definition leftpad
  signature: (n : Nat) (c : Char := ' ') (s : String)
  body: ofList (List.leftpad n c s.toList)

中文:
定义 leftpad
  签名: (n : 自然数) (c : Char := ' ') (s : String)
  定义体: ofList (List.leftpad n c s.toList)
-/
def leftpad (n : Nat) (c : Char := ' ') (s : String) : String :=
  ofList (List.leftpad n c s.toList)

/--
Definition of `replicate` / `replicate` 的定义

English:
definition replicate
  signature: (n : Nat) (c : Char)
  body: ofList (List.replicate n c)

中文:
定义 replicate
  签名: (n : 自然数) (c : Char)
  定义体: ofList (List.replicate n c)

Depends on / 依赖: List.replicate, ofList, replicate
-/
def replicate (n : Nat) (c : Char) : String :=
  ofList (List.replicate n c)

-- TODO bring this definition in line with the above, either by:
-- adding `List.rightpad` to Batteries and changing the definition of `rightpad` here to match
-- or by changing the definition of `leftpad` above to match this
/--
Definition of `rightpad` / `rightpad` 的定义

English:
definition rightpad
  signature: (n : Nat) (c : Char := ' ') (s : String)
  body: s ++ String.replicate (n - s.length) c

中文:
定义 rightpad
  签名: (n : 自然数) (c : Char := ' ') (s : String)
  定义体: s ++ String.replicate (n - s.length) c
-/
def rightpad (n : Nat) (c : Char := ' ') (s : String) : String :=
  s ++ String.replicate (n - s.length) c

/--
Definition of `IsPrefix` / `IsPrefix` 的定义

English:
definition IsPrefix
  signature: : String -> String -> Prop

中文:
定义 IsPrefix
  签名: : String -> String -> 命题
-/
def IsPrefix : String -> String -> Prop
  | d1, d2 => List.IsPrefix d1.toList d2.toList

/--
Definition of `IsSuffix` / `IsSuffix` 的定义

English:
definition IsSuffix
  signature: : String -> String -> Prop

中文:
定义 IsSuffix
  签名: : String -> String -> 命题
-/
def IsSuffix : String -> String -> Prop
  | d1, d2 => List.IsSuffix d1.toList d2.toList

/--
Definition of `mapTokens` / `mapTokens` 的定义

English:
definition mapTokens
  signature: (c : Char) (f : String -> String)
  body: intercalate (singleton c) ∘ List.map f ∘ (·.splitToList (· = c))

中文:
定义 mapTokens
  签名: (c : Char) (f : String -> String)
  定义体: intercalate (singleton c) ∘ List.map f ∘ (·.splitToList (· = c))

Depends on / 依赖: List.map, intercalate, singleton, splitToList
-/
def mapTokens (c : Char) (f : String -> String) : String -> String :=
  intercalate (singleton c) ∘ List.map f ∘ (·.splitToList (· = c))

/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: (s : String)
  body: s.front

中文:
定义 head
  签名: (s : String)
  定义体: s.front

Depends on / 依赖: s.front
-/
def head (s : String) : Char :=
  s.front

end String
