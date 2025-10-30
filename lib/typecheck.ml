open Core
open Nbe

type context = ty_value list

let rec infer (ctx : context) (lvl : int) : tm -> ty_value = function
  | Var n -> ( try List.nth ctx n with _ -> failwith "out of scope")
  | App (f, a) -> (
      let f_ty = infer ctx lvl f in
      match f_ty with
      | PiV (a_ty, b_ty_clos) ->
          check ctx lvl a a_ty;
          let a_val = eval [] a in
          instantiate b_ty_clos a_val
      | _ -> failwith "expected function type in application")
  | Lambda _ -> failwith ""

and check (ctx : context) (lvl : int) (t : tm) (ty : ty_value) : unit =
  match (t, ty) with
  | Lambda body, PiV (a_ty, b_ty_clos) ->
      let var_neutral = Neutral (Local lvl, [], lazy (Abstract a_ty)) in
      let b_ty = instantiate b_ty_clos var_neutral in
      check (a_ty :: ctx) (lvl + 1) body b_ty
  | _ ->
      let inferred_ty = infer ctx lvl t in
      if conv_ty inferred_ty ty lvl then () else failwith "type mismatch"

let rec infer_ty (ctx : context) (lvl : int) : ty -> ty_value = function
  | Star -> failwith ""
  | Pi (a, b) ->
      let a_val = eval_ty [] a in
      let _ = infer_ty ctx lvl a in
      let _var_neutral = Neutral (Local lvl, [], lazy (Abstract a_val)) in
      let _ = infer_ty (a_val :: ctx) (lvl + 1) b in
      StarV
  | TVar n -> (
      try List.nth ctx n with _ -> failwith "type variable out of scope")

type elab_mode =
  | Infer
  | Check of ty_value

type elab_result = {
  term : tm;
  ty : ty_value;
}

let elab_tm (ctx : context) (lvl : int) (mode : elab_mode) (t : tm) :
    elab_result =
  match mode with
  | Infer ->
      let ty = infer ctx lvl t in
      { term = t; ty }
  | Check expected_ty ->
      check ctx lvl t expected_ty;
      { term = t; ty = expected_ty }

let elab_tm_infer (ctx : context) (lvl : int) (t : tm) : elab_result =
  elab_tm ctx lvl Infer t

let elab_tm_check (ctx : context) (lvl : int) (t : tm) (ty : ty_value) : tm =
  let result = elab_tm ctx lvl (Check ty) t in
  result.term
