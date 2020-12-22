

open System
exception InferException of string


type Type =
    | NamedType of string
    | VarType of string
    | FunctionType of param: Type * body : Type
    | ForAllType of quantifiers: string[] * tp : Type

type Expression =
    | IntExp of int
    | VarExp of string
    | FunctionExp of param : string * body: Expression
    | CallExp of func : Expression * arg: Expression
    | IfExp of cond: Expression *  trueBranch : Expression * falseBranch: Expression
    | LetExp of name : string * rhs: Expression * body : Expression


let rec typeToString(t: Type) =
    match t with
    | NamedType n -> n
    | VarType n -> n
    | FunctionType(param, body) -> "(" + typeToString(param) + ") -> (" + typeToString(body) + ")"




let mutable num = 0

let newTVar () =
    num <- num + 1
    VarType("Type_" + string num)


//----------------------------------------------------------------------------

// Substitution
let rec applySubstToType(subst: Map<string, Type>, t: Type) =
    match t with
    | NamedType _ -> t
    | VarType name ->
        match subst.TryFind(name) with
        | Some(v) -> v
        | None -> t
    | FunctionType(param, body) ->
        FunctionType(param = applySubstToType(subst, param),
                     body = applySubstToType(subst, body))
    | ForAllType(quantifiers,  tp) ->
        let mutable substWithoutBound = subst
        for quantifier in quantifiers do
            substWithoutBound <- substWithoutBound.Remove(quantifier)

        ForAllType(quantifiers = quantifiers, tp = applySubstToType(substWithoutBound, tp))



let applySubstToEnv(subst: Map<string, Type>, env: Map<string, Type>) =

    let mutable env2 = env
    for KeyValue(name, t) in env do
        env2  <- env2.Add(name, applySubstToType(subst, t))

    env2

//----------------------------------------------------------------------------

let rec contains(name: string, t: Type) =
    match t with
    | NamedType _ -> false
    | VarType n -> n = name
    | FunctionType(param, body) ->
        contains(name, param)
        || contains(name, body)


let varBind(name: string, t: Type) =
    match t with
    | VarType n when n = name -> Map.empty
    | _ ->
        if (contains(name, t)) then
            raise(InferException("Type " + typeToString(t) + " contains a reference to itself"))
        else
            Map.empty.Add(name, t)



let composeSubst(s1 : Map<string, Type>, s2: Map<string, Type>) =
    let mutable m = Map.empty<string, Type>
    for KeyValue(name, t) in s2 do
        m <- m.Add(name, applySubstToType(s1, t))

    let mutable result = s1
    for KeyValue(name, t) in m do
        result <- result.Add(name, t)

    result




let rec unify(t1: Type, t2: Type) =
    match (t1, t2) with
    | (NamedType(name1), NamedType(name2)) when name1 = name2 -> Map.empty
    | (VarType(name), _) -> varBind(name, t2)
    | (_, VarType(name)) -> varBind(name, t1)
    | (FunctionType(p1, b1), FunctionType(p2, b2)) ->
        let s1 = unify(p1, p2)
        let s2 = unify(applySubstToType(s1, b1), applySubstToType(s1, b2))
        composeSubst(s1, s2)

    | _ -> raise(InferException("Type mismatch:\n    Expected " + typeToString(t1) + "\n    Found " + typeToString(t2)))





//----------------------------------------------------------------------------


let tFunc(types) =
    types |> Array.reduceBack (fun p b  -> FunctionType(p, b))



//let c(f: Expression, args) =
//    args |> Array.fold (fun f a -> CallExp(func = f, arg = a)) f
//
// let call1 = c(VarExp("+"), [| IntExp(1); IntExp(2) |])
let call(args) =
    args |> Array.reduce (fun f a -> CallExp(func = f, arg = a))



//----------------------------------------------------------------------------
// let





let union(freeVars1: Map<string, bool>, freeVars2: Map<string, bool>) =
    let mutable fvs = freeVars1
    for KeyValue(name, b) in freeVars2 do
        fvs  <- fvs.Add(name, b)

    fvs

let difference(freeVars1: Map<string, bool>, freeVars2: Map<string, bool>) =
    let mutable fvs = freeVars1
    for KeyValue(name, _) in freeVars2 do
        fvs  <- fvs.Remove(name)

    fvs


let rec freeTypeVarsInType(t : Type) =
    match t with
    | NamedType _ -> Map.empty
    | VarType name -> Map.empty.Add(name, true)
    | FunctionType(param, body) -> union(freeTypeVarsInType(param), freeTypeVarsInType(body))
    | ForAllType(quantifiers, tp) ->
        let mutable freeVars = Map.empty;
        for quantifier in quantifiers do
            freeVars <- freeVars.Add(quantifier, true)

        let freeInType = freeTypeVarsInType(tp)
        difference(freeInType, freeVars)


let freeTypeVarsInEnv(env: Map<string, Type>) =
    let mutable freeVars = Map.empty
    for KeyValue(_, t) in env do
        freeVars <- union(freeVars, freeTypeVarsInType(t))

    freeVars


let generalize(env: Map<string, Type>, t : Type) =
    let typeFreeVars = freeTypeVarsInType(t)
    let envFreeVars = freeTypeVarsInEnv(env)

    let quantifiers = difference(typeFreeVars, envFreeVars)
                      |> Map.toArray
                      |> Array.map fst

    if quantifiers.Length > 0 then
        ForAllType(quantifiers = quantifiers, tp = t)
    else
        t




//----------------------------------------------------------------------------






let rec infer(env : Map<string, Type>, exp: Expression) =
    match exp with
    | IntExp(_) -> ( NamedType("Int"), Map.empty<string, Type> )

//    | VarExp(name) ->
//        match env.TryFind(name) with
//        | Some(t) -> ( t, Map.empty<string, Type> )
//        | None -> raise(InferException("Unbound var" + name))

    | VarExp(name) ->
        match env.TryFind(name) with
        | Some(t) ->
            match t with
            | ForAllType(quantifiers, tp) ->
                // instantiate
                let mutable subst = Map.empty
                for quantifier in quantifiers do
                    subst <- subst.Add(quantifier, newTVar())

                (applySubstToType(subst, tp), Map.empty)

            | _ -> ( t, Map.empty )
        | None -> raise(InferException("Unbound var" + name))


    | FunctionExp(param, body)  ->
        let nT = newTVar()
        let nEnv = env.Add(param, nT)
        let (tBody, subst) = infer(nEnv, body)
        (FunctionType(param = applySubstToType(subst, nT),
                      body = tBody), subst)

    | LetExp(name, rhs, body) ->
        let (rhsType, s1) = infer(env, rhs)
        let env1 = applySubstToEnv(s1, env)
        let rhsPolyType = generalize(env1, rhsType)
        let env2 = env1.Add(name, rhsPolyType)
        let (bodyType, s2) = infer(env2, body)
        let s3 = composeSubst(s1, s2)

        (bodyType, s3)
    // CallExp, IfExp 部分简化, 是否可行?
    | CallExp(func, arg) ->
        let (funcType, s1) = infer(env, func)
        let (argType, s2) = infer(applySubstToEnv(s1, env), arg)
        let s3 = composeSubst(s1, s2)

        let nVar = newTVar()
        let s4 = unify(FunctionType(argType, nVar), funcType)
        let resultSubst = composeSubst(s3, s4)

        match applySubstToType(s4, funcType) with
        | FunctionType(_, body) -> (body, resultSubst)
        | t -> raise(InferException(typeToString(t)))

    | IfExp(cond, trueBranch, falseBranch) ->
        let (condType, s0) = infer(env, cond)
        let s1 = unify(condType, NamedType("bool"))
        let s2 = composeSubst(s0, s1)

        let env1 = applySubstToEnv(s2, env)
        let (trueBranchType, s3) = infer(env1, trueBranch)
        let (falseBranchType, s4) = infer(env1, falseBranch)


        let s5 = composeSubst(composeSubst(s2, s3), s4)
        let trueBranchType1 = applySubstToType(s5, trueBranchType)
        let falseBranchType1 = applySubstToType(s5, falseBranchType)
        let s6 = unify(trueBranchType1, falseBranchType1)
        let resultSubst = composeSubst(s5, s6)

        (applySubstToType(s6, trueBranchType1), resultSubst)

    | _ ->  raise(InferException("NotImplemented"))

// 原文实现:
//    | CallExp(func, arg) ->
//        let (funcType, s1) = infer(env, func)
//        let (argType, s2) = infer(applySubstToEnv(s1, env), arg)
//        let s3 = composeSubst(s1, s2)
//
//        let nVar = newTVar()
//        let s4 = unify(FunctionType(argType, nVar), funcType)
//        let funcType1 = applySubstToType(s4, funcType)
//
//        let s5 = composeSubst(s3, s4)
//        let s6 =
//            match funcType1 with
//            | FunctionType(param, _) -> unify(applySubstToType(s5, param), argType)
//            | _ -> raise(InferException(typeToString(funcType1)))
//
//        let resultSubst = composeSubst(s5, s6)
//
//        match funcType1 with
//        | FunctionType(_, body) -> (applySubstToType(resultSubst, body), resultSubst)
//        | _ -> raise(InferException(typeToString(funcType1)))
//
//    | IfExp(cond, trueBranch, falseBranch) ->
//        let (condType, s0) = infer(env, cond)
//        let s1 = unify(condType, NamedType("bool"))
//
//        let env1 = applySubstToEnv(composeSubst(s0, s1), env)
//        let (trueBranchType, s2) = infer(env1, trueBranch)
//        let s3 = composeSubst(s1, s2)
//
//        let env2 = applySubstToEnv(s2, env1)
//        let (falseBranchType, s4) = infer(env2, falseBranch)
//        let s5 = composeSubst(s3, s4)
//
//        let trueBranchType1 = applySubstToType(s5, trueBranchType)
//        let falseBranchType1 = applySubstToType(s5, falseBranchType)
//        let s6 = unify(trueBranchType1, falseBranchType1)
//        let resultSubst = composeSubst(s5, s6)
//
//        (applySubstToType(s6, trueBranchType1), resultSubst)
//
//








let env = Map.empty
              .Add("true", NamedType("Bool"))
              .Add("false", NamedType("Bool"))
              .Add("!", tFunc([| NamedType("Bool"); NamedType("Bool") |]))
              .Add("&&", tFunc([| NamedType("Bool"); NamedType("Bool"); NamedType("Bool") |]))
              .Add("||", tFunc([| NamedType("Bool"); NamedType("Bool"); NamedType("Bool") |]))
              .Add("Int==", tFunc([| NamedType("Int"); NamedType("Int"); NamedType("Bool") |]))
              .Add("Bool==", tFunc([| NamedType("Bool"); NamedType("Bool"); NamedType("Bool") |]))
              .Add("==", ForAllType(quantifiers = [| "A" |], tp = tFunc([| VarType("A"); VarType("A"); NamedType("Bool") |])))
              .Add("+", tFunc([| NamedType("Int"); NamedType("Int"); NamedType("Int") |]))



let test1 () =
    printfn "------------------------"
    printfn "Test: 1 + 2"
    try
        // 1 + 2
        let c = call([| VarExp("+"); IntExp(1); IntExp(2) |])
        let (t, _) = infer(env, c)
        printfn "%A" (typeToString(t))
    with
    | InferException(message) -> printfn "%A" message

let test2 () =
    printfn "------------------------"
    printfn "Test: true + false"
    try
        let c = call([| VarExp("+"); VarExp("true"); VarExp("false") |])
        let (t, _) = infer(env, c)
        printfn "%A" (typeToString(t))
    with
    | InferException(message) -> printfn "%A" message


let test3 () =
    printfn "------------------------"
    printfn "Test: let id = x -> x in id(i)"
    try
        let c = LetExp(name = "id",
                       rhs = FunctionExp(param = "x",
                                         body = VarExp("x")),
                       body = CallExp(func = VarExp("id"),
                                      arg = IntExp(1)))
        let (t, _) = infer(env, c)
        printfn "%A" (typeToString(t))
    with
    | InferException(message) -> printfn "%A" message

let test4 () =
    printfn "------------------------"
    printfn "Test: let id = x -> x in id(true)"
    try
        let c = LetExp(name = "id",
                       rhs = FunctionExp(param = "x",
                                         body = VarExp("x")),
                       body = CallExp(func = VarExp("id"),
                                      arg = VarExp("true")))
        let (t, _) = infer(env, c)
        printfn "%A" (typeToString(t))
    with
    | InferException(message) -> printfn "%A" message


let test5 () =
    printfn "------------------------"
    printfn "Test: let id = x -> x in (id(1) == id(1)) == id(true)"
    try
        let c = LetExp(name = "id",
                       rhs = FunctionExp(param = "x",
                                         body = VarExp("x")),
                       body = call([| VarExp("==")
                                      call([| VarExp("==")
                                              call([| VarExp("id"); IntExp(1) |])
                                              call([| VarExp("id"); IntExp(1) |])|])
                                      call([| VarExp("id");  VarExp("true") |]) |]))

        let (t, _) = infer(env, c)
        printfn "%A" (typeToString(t))

    with
    | InferException(message) -> printfn "%A" message



[<EntryPoint>]
let main _ =
    test1()
    test2()
    test3()
    test4()
    test5()
    0


