/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Lean
import MySql.SQLDSL

open Lean Elab Meta

namespace MySql

declare_syntax_cat      parsId
syntax ident          : parsId
syntax "(" parsId ")" : parsId

declare_syntax_cat           selectField
syntax parsId              : selectField
syntax parsId " AS " ident : selectField

declare_syntax_cat                 sqlSelect
syntax "*"                       : sqlSelect
syntax "DISTINCT " "*"           : sqlSelect
syntax selectField,+             : sqlSelect
syntax "DISTINCT " selectField,+ : sqlSelect

declare_syntax_cat           entry
syntax num                 : entry
syntax "-" noWs num        : entry
syntax str                 : entry
syntax scientific          : entry
syntax "-" noWs scientific : entry
syntax "NULL"              : entry
syntax "(" entry ")"       : entry

declare_syntax_cat propSymbol
syntax " = "     : propSymbol
syntax " <> "    : propSymbol
syntax " != "    : propSymbol
syntax " < "     : propSymbol
syntax " <= "    : propSymbol
syntax " > "     : propSymbol
syntax " >= "    : propSymbol

declare_syntax_cat                prop
syntax "TRUE"                   : prop
syntax "FALSE"                  : prop
syntax parsId propSymbol parsId : prop
syntax parsId propSymbol entry  : prop
syntax prop " AND " prop        : prop
syntax prop " OR "  prop        : prop
syntax " NOT " prop             : prop
syntax "(" prop ")"             : prop

declare_syntax_cat join
syntax " INNER " : join
syntax " LEFT "  : join
syntax " RIGHT " : join
syntax " OUTER " : join

declare_syntax_cat                                 sqlFrom
syntax ident                                     : sqlFrom
syntax sqlFrom ", " sqlFrom                      : sqlFrom
syntax sqlFrom " AS " ident                      : sqlFrom
syntax sqlFrom join " JOIN " sqlFrom " ON " prop : sqlFrom
syntax "(" sqlFrom ")"                           : sqlFrom

syntax (name := query) "SELECT " sqlSelect " FROM " sqlFrom (" WHERE " prop)? : term

def mkStrOfIdent (id : Syntax) : Expr :=
  mkStrLit id.getId.toString

partial def elabStrOfParsId : Syntax → TermElabM Expr
  | `(parsId|$id:ident)      => pure $ mkStrLit id.getId.toString
  | `(parsId|($pars:parsId)) => elabStrOfParsId pars
  | _                        => throwUnsupportedSyntax

def elabCol : TSyntax `selectField → TermElabM Expr
  | `(selectField|$c:parsId)             => do
    mkAppM `MySql.SQLSelectField.col #[← elabStrOfParsId c]
  | `(selectField|$c:parsId AS $a:ident) => do
    mkAppM `MySql.SQLSelectField.alias #[← elabStrOfParsId c, mkStrOfIdent a]
  | _                                    => throwUnsupportedSyntax

def elabSelect : Syntax → TermElabM Expr
  | `(sqlSelect|*)                          => mkAppM `MySql.SQLSelect.all #[mkConst ``false]
  | `(sqlSelect|DISTINCT *)                 => mkAppM `MySql.SQLSelect.all #[mkConst ``true]
  | `(sqlSelect|$cs:selectField,*)          => do
    let cols ← mkListLit (mkConst `MySql.SQLSelectField) (← cs.getElems.toList.mapM elabCol)
    mkAppM `MySql.SQLSelect.list #[mkConst ``false, cols]
  | `(sqlSelect|DISTINCT $cs:selectField,*) => do
    let cols ← mkListLit (mkConst `MySql.SQLSelectField) (← cs.getElems.toList.mapM elabCol)
    mkAppM `MySql.SQLSelect.list #[mkConst ``true, cols]
  | _                                       => throwUnsupportedSyntax

def mkApp' (name : Name) (e : Expr) : Expr :=
  mkApp (mkConst name) e

def elabConst (name : Name) : TermElabM Expr :=
  pure $ mkConst name

def negFloat (f : Float) : Float :=
  -1.0 * f

partial def elabEntry : TSyntax `entry → TermElabM Expr
  | `(entry|$v:num)            =>
    mkAppM `MySql.DataEntry.EInt #[mkApp' `Int.ofNat (mkNatLit v.getNat)]
  | `(entry|-$v:num)           =>
    mkAppM `MySql.DataEntry.EInt $ match v.getNat with
      | Nat.zero   => #[mkApp' `Int.ofNat (mkConst `Nat.zero)]
      | Nat.succ n => #[mkApp' `Int.negSucc (mkNatLit n)]
  | `(entry|$v:scientific)  => do
    mkAppM `MySql.DataEntry.EFloat #[← Term.elabScientificLit v (mkConst `Float)]
  | `(entry|-$v:scientific) => do
    let f ← Term.elabScientificLit v (mkConst `Float)
    mkAppM `MySql.DataEntry.EFloat #[mkApp' `negFloat f]
  | `(entry|$v:str)            =>
    mkAppM `MySql.DataEntry.EString #[mkStrLit v.getString]
  | `(entry|NULL)              => elabConst `MySql.DataEntry.ENull
  | `(entry|($e:entry))        => elabEntry e
  | _                          => throwUnsupportedSyntax

def elabPropSymbol (stx : Syntax) (isEntry : Bool) : TermElabM Name :=
  match stx with
  | `(propSymbol|=)  => pure $ if isEntry then `MySql.SQLProp.eqE else `MySql.SQLProp.eqC
  | `(propSymbol|<>) => pure $ if isEntry then `MySql.SQLProp.neE else `MySql.SQLProp.neC
  | `(propSymbol|!=) => pure $ if isEntry then `MySql.SQLProp.neE else `MySql.SQLProp.neC
  | `(propSymbol|<)  => pure $ if isEntry then `MySql.SQLProp.ltE else `MySql.SQLProp.ltC
  | `(propSymbol|<=) => pure $ if isEntry then `MySql.SQLProp.leE else `MySql.SQLProp.leC
  | `(propSymbol|>)  => pure $ if isEntry then `MySql.SQLProp.gtE else `MySql.SQLProp.gtC
  | `(propSymbol|>=) => pure $ if isEntry then `MySql.SQLProp.geE else `MySql.SQLProp.geC
  | _                => throwUnsupportedSyntax

partial def elabProp : Syntax → TermElabM Expr
  | `(prop|TRUE)                              => elabConst `MySql.SQLProp.tt
  | `(prop|FALSE)                             => elabConst `MySql.SQLProp.ff
  | `(prop|$l:parsId $s:propSymbol $r:parsId) => do
    mkAppM (← elabPropSymbol s false) #[← elabStrOfParsId l, ← elabStrOfParsId r]
  | `(prop|$c:parsId $s:propSymbol $e:entry)  => do
    mkAppM (← elabPropSymbol s true) #[← elabStrOfParsId c, ← elabEntry e]
  | `(prop|$l:prop AND $r:prop)               => do
    mkAppM `MySql.SQLProp.and #[← elabProp l, ← elabProp r]
  | `(prop|$l:prop OR $r:prop)                => do
    mkAppM `MySql.SQLProp.or #[← elabProp l, ← elabProp r]
  | `(prop|NOT $p:prop)                       => do
    mkAppM `MySql.SQLProp.not #[← elabProp p]
  | `(prop|($p:prop))                         => elabProp p
  | _                                         => throwUnsupportedSyntax

def elabJoin : Syntax → TermElabM Expr
  | `(join|INNER) => elabConst `MySql.SQLJoin.inner
  | `(join|LEFT)  => elabConst `MySql.SQLJoin.left
  | `(join|RIGHT) => elabConst `MySql.SQLJoin.right
  | `(join|OUTER) => elabConst `MySql.SQLJoin.outer
  | _             => throwUnsupportedSyntax

partial def elabFrom : Syntax → TermElabM Expr
  | `(sqlFrom|$t:ident)               => mkAppM `MySql.SQLFrom.table #[mkStrOfIdent t]
  | `(sqlFrom|$f:sqlFrom AS $t:ident) => do
    mkAppM `MySql.SQLFrom.alias #[← elabFrom f, mkStrOfIdent t]
  | `(sqlFrom|$t₁:sqlFrom, $t₂:sqlFrom) => do mkAppM `MySql.SQLFrom.implicitJoin #[← elabFrom t₁, ← elabFrom t₂]
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom ON $p:prop) => do
    mkAppM `MySql.SQLFrom.join #[← elabJoin j, ← elabFrom l, ← elabFrom r, ← elabProp p]
  | `(sqlFrom|($f:sqlFrom))           => elabFrom f
  | _                                 => throwUnsupportedSyntax

@[term_elab query] def elabQuery : Term.TermElab := fun stx _ =>
  match stx with
  | `(query| SELECT $sel FROM $frm $[WHERE $prp]?) => do
    let whr ← match prp with
    | none     => elabConst `MySql.SQLProp.tt
    | some prp => elabProp prp
    mkAppM `MySql.SQLQuery.mk #[← elabSelect sel, ← elabFrom frm, whr]
  | _ => throwUnsupportedSyntax
