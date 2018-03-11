use super::*;
use test_utils::*;

#[test]
fn test_queries_on_facts()
{
    let mut wam = Machine::new();

    submit(&mut wam, "p(Z, Z).");
    submit(&mut wam, "clouds(are, nice).");
    submit(&mut wam, "are(X, great) :- are(X, nice).");
    submit(&mut wam, "are(great) :- are(X, nice).");

    assert_prolog_success!(&mut wam, "?- p(Z, Z).", [["Z = _0"]]);
    assert_prolog_success!(&mut wam, "?- p(Z, z).", [["Z = z"]]);
    assert_prolog_success!(&mut wam, "?- p(Z, w).", [["Z = w"]]);

    assert_prolog_failure!(&mut wam, "?- p(z, w).");

    assert_prolog_success!(&mut wam, "?- p(w, w).");

    assert_prolog_failure!(&mut wam, "?- clouds(Z, Z).");

    assert_prolog_success!(&mut wam, "?- clouds(are, Z).", [["Z = nice"]]);
    assert_prolog_success!(&mut wam, "?- clouds(Z, nice).", [["Z = are"]]);

    submit(&mut wam, "p(Z, h(Z, W), f(W)).");

    assert_prolog_failure!(&mut wam, "?- p(z, h(z, z), f(w)).");
    assert_prolog_success!(&mut wam, "?- p(z, h(z, w), f(w)).");
    assert_prolog_success!(&mut wam, "?- p(z, h(z, W), f(w)).", [["W = w"]]);
    assert_prolog_success!(&mut wam, "?- p(Z, h(Z, w), f(Z)).", [["Z = w"]]);
    assert_prolog_failure!(&mut wam, "?- p(z, h(Z, w), f(Z)).");

    submit(&mut wam, "p(f(X), h(Y, f(a)), Y).");

    assert_prolog_success!(&mut wam, "?- p(Z, h(Z, W), f(W)).", [["W = f(a)", "Z = f(f(a))"]]);
}

#[test]
fn test_queries_on_rules() {
    let mut wam = Machine::new();

    submit(&mut wam, "p(X, Y) :- q(X, Z), r(Z, Y).");
    submit(&mut wam, "q(q, s).");
    submit(&mut wam, "r(s, t).");

    assert_prolog_success!(&mut wam, "?- p(X, Y).", [["Y = t", "X = q"]]);
    assert_prolog_success!(&mut wam, "?- p(q, t).");
    assert_prolog_failure!(&mut wam, "?- p(t, q).");
    assert_prolog_success!(&mut wam, "?- p(q, T).", [["T = t"]]);
    assert_prolog_failure!(&mut wam, "?- p(t, t).");

    submit(&mut wam, "p(X, Y) :- q(f(f(X)), R), r(S, T).");
    submit(&mut wam, "q(f(f(X)), r).");

    assert_prolog_success!(&mut wam, "?- p(X, Y).", [["X = _0", "Y = _1"]]);

    submit(&mut wam, "q(f(f(x)), r).");

    assert_prolog_success!(&mut wam, "?- p(X, Y).", [["X = x", "Y = _1"]]);

    submit(&mut wam, "p(X, Y) :- q(X, Y), r(X, Y).");
    submit(&mut wam, "q(s, t).");
    submit(&mut wam, "r(X, Y) :- r(a).");
    submit(&mut wam, "r(a).");

    assert_prolog_success!(&mut wam, "?- p(X, Y).", [["X = s", "Y = t"]]);
    assert_prolog_failure!(&mut wam, "?- p(t, S).");
    assert_prolog_success!(&mut wam, "?- p(s, T).", [["T = t"]]);
    assert_prolog_success!(&mut wam, "?- p(S, t).", [["S = s"]]);

    submit(&mut wam, "p(f(f(a), g(b), X), g(b), h) :- q(X, Y).");
    submit(&mut wam, "q(X, Y).");

    assert_prolog_success!(&mut wam,  "?- p(f(X, Y, Z), g(b), h).",
                           [["Z = _3", "Y = g(b)", "X = f(a)"]]);
    assert_prolog_failure!(&mut wam, "?- p(f(X, g(Y), Z), g(Z), X).");
    assert_prolog_success!(&mut wam, "?- p(f(X, g(Y), Z), g(Z), h).",
                           [["Z = b", "Y = b", "X = f(a)"]]);
    assert_prolog_success!(&mut wam, "?- p(Z, Y, X).",
                           [["X = h", "Y = g(b)", "Z = f(f(a), g(b), _7)"]]);
    assert_prolog_success!(&mut wam, "?- p(f(X, Y, Z), Y, h).",
                           [["Y = g(b)", "Z = _3", "X = f(a)"]]);

    submit(&mut wam, "p(_, f(_, Y, _)) :- h(Y).");
    submit(&mut wam, "h(y).");

    assert_prolog_success!(&mut wam, "?- p(_, f(_, Y, _)).", [["Y = y"]]);
    assert_prolog_success!(&mut wam, "?- p(_, f(_, y, _)).");
    assert_prolog_failure!(&mut wam, "?- p(_, f(_, z, _)).");
}

#[test]
fn test_queries_on_predicates() {
    let mut wam = Machine::new();

    submit(&mut wam, "p(X, a). p(b, X).");

    assert_prolog_success!(&mut wam, "?- p(x, Y).", [["Y = a"]]);
    assert_prolog_success!(&mut wam, "?- p(X, a).", [["X = _0"],  // 1st case
                                                     ["X = b"]]); // 2nd case.
    assert_prolog_success!(&mut wam, "?- p(b, X).", [["X = a"],  // 1st case
                                                     ["X = _0"]]); // 2nd case.
    assert_prolog_success!(&mut wam, "?- p(X, X).", [["X = a"],
                                                     ["X = b"]]);
    assert_prolog_success!(&mut wam, "?- p(b, a).");
    assert_prolog_failure!(&mut wam, "?- p(a, b).");

    submit(&mut wam, "p(X, Y, a). p(X, a, Y). p(X, Y, a).");

    assert_prolog_success!(&mut wam, "?- p(c, d, X).", [["X = a"],
                                                        ["X = a"]]);
    assert_prolog_success!(&mut wam, "?- p(a, a, a).");
    assert_prolog_failure!(&mut wam, "?- p(b, c, d).");

    submit(&mut wam, "p(X, a). p(X, Y) :- q(Z), p(X, X).");

    assert_prolog_success!(&mut wam, "?- p(X, Y).", [["X = _0", "Y = a"]]);
    assert_prolog_success!(&mut wam, "?- p(x, a).");
    assert_prolog_success!(&mut wam, "?- p(X, a).", [["X = _0"]]);
    assert_prolog_failure!(&mut wam, "?- p(X, b).");

    submit(&mut wam, "q(z).");

    assert_prolog_success_with_limit!(&mut wam, "?- p(X, b).", [["X = a"],
                                                                ["X = a"],
                                                                ["X = a"]],
                                      3);
    assert_prolog_success!(&mut wam, "?- p(x, a).");
    assert_prolog_success_with_limit!(&mut wam, "?- p(X, Y).", [["X = _0", "Y = a"],
                                                                ["Y = _1", "X = a"],
                                                                ["Y = _1", "X = a"]],
                                      3);

    submit(&mut wam, "p(X, a). p(X, Y) :- q(Y), p(X, X).");

    assert_prolog_success_with_limit!(&mut wam, "?- p(X, Y).", [["X = _0", "Y = a"],
                                                                ["Y = z", "X = a"]],
                                      2);
    assert_prolog_failure!(&mut wam, "?- p(X, b).");

    submit(&mut wam, "p(a, z). p(X, Y) :- q(Y), p(X, Y).");

    assert_prolog_success_with_limit!(&mut wam, "?- p(X, Y).", [["X = a", "Y = z"],
                                                                ["X = a", "Y = z"]],
                                      2);

    assert_prolog_success_with_limit!(&mut wam, "?- p(X, z).", [["X = a"],
                                                                ["X = a"]],
                                      2);
    assert_prolog_success!(&mut wam, "?- p(a, z).");
    assert_prolog_success_with_limit!(&mut wam, "?- p(a, X).", [["X = z"],
                                                                ["X = z"]],
                                      2);
    assert_prolog_failure!(&mut wam, "?- p(b, a).");

    submit(&mut wam, "p(X, Y, Z) :- q(X), r(Y), s(Z).
                      p(a, b, Z) :- q(Z).");

    submit(&mut wam, "q(x).");
    submit(&mut wam, "r(y).");
    submit(&mut wam, "s(z).");

    assert_prolog_success!(&mut wam, "?- p(X, Y, Z).", [["Y = y", "X = x", "Z = z"],
                                                        ["Y = b", "X = a", "Z = x"]]);
    assert_prolog_failure!(&mut wam, "?- p(a, b, c).");
    assert_prolog_success!(&mut wam, "?- p(a, b, C).", [["C = x"]]);

    submit(&mut wam, "p(X) :- q(X). p(X) :- r(X).");
    submit(&mut wam, "q(X) :- a.");
    submit(&mut wam, "r(X) :- s(X, t). r(X) :- t(X, u).");

    submit(&mut wam, "s(x, t).");
    submit(&mut wam, "t(y, u).");

    assert_prolog_success!(&mut wam, "?- p(X).", [["X = x"],
                                                  ["X = y"]]);
    assert_prolog_success!(&mut wam, "?- p(x).");
    assert_prolog_success!(&mut wam, "?- p(y).");
    assert_prolog_failure!(&mut wam, "?- p(z).");

    submit(&mut wam, "p(f(f(X)), h(W), Y) :- g(W), h(W), f(X).
                      p(X, Y, Z) :- h(Y), g(W), z(Z).");
    submit(&mut wam, "g(f(X)) :- z(X). g(X) :- h(X).");
    submit(&mut wam, "h(w). h(x). h(z).");
    submit(&mut wam, "f(s).");
    submit(&mut wam, "z(Z).");

    assert_prolog_success!(&mut wam, "?- p(X, Y, Z).", [["Y = h(w)", "X = f(f(s))", "Z = _2"],
                                                        ["Y = h(x)", "X = f(f(s))", "Z = _2"],
                                                        ["Y = h(z)", "X = f(f(s))", "Z = _2"],
                                                        ["Y = w", "Z = _2", "X = _0"],
                                                        ["Y = w", "Z = _2", "X = _0"],
                                                        ["Y = w", "Z = _2", "X = _0"],
                                                        ["Y = w", "Z = _2", "X = _0"],
                                                        ["Y = x", "Z = _2", "X = _0"],
                                                        ["Y = x", "Z = _2", "X = _0"],
                                                        ["Y = x", "Z = _2", "X = _0"],
                                                        ["Y = x", "Z = _2", "X = _0"],
                                                        ["Y = z", "Z = _2", "X = _0"],
                                                        ["Y = z", "Z = _2", "X = _0"],
                                                        ["Y = z", "Z = _2", "X = _0"],
                                                        ["Y = z", "Z = _2", "X = _0"]]);
    assert_prolog_success!(&mut wam, "?- p(X, X, Z).", [["Z = _1", "X = w"],
                                                        ["Z = _1", "X = w"],
                                                        ["Z = _1", "X = w"],
                                                        ["Z = _1", "X = w"],
                                                        ["Z = _1", "X = x"],
                                                        ["Z = _1", "X = x"],
                                                        ["Z = _1", "X = x"],
                                                        ["Z = _1", "X = x"],
                                                        ["Z = _1", "X = z"],
                                                        ["Z = _1", "X = z"],
                                                        ["Z = _1", "X = z"],
                                                        ["Z = _1", "X = z"]]);
    assert_prolog_success!(&mut wam, "?- p(f(f(Z)), Y, Z).", [["Y = h(w)", "Z = s"],
                                                              ["Y = h(x)", "Z = s"],
                                                              ["Y = h(z)", "Z = s"],
                                                              ["Y = w", "Z = _1"],
                                                              ["Y = w", "Z = _1"],
                                                              ["Y = w", "Z = _1"],
                                                              ["Y = w", "Z = _1"],
                                                              ["Y = x", "Z = _1"],
                                                              ["Y = x", "Z = _1"],
                                                              ["Y = x", "Z = _1"],
                                                              ["Y = x", "Z = _1"],
                                                              ["Y = z", "Z = _1"],
                                                              ["Y = z", "Z = _1"],
                                                              ["Y = z", "Z = _1"],
                                                              ["Y = z", "Z = _1"]]);
    assert_prolog_success!(&mut wam, "?- p(X, X, X).", [["X = w"],
                                                        ["X = w"],
                                                        ["X = w"],
                                                        ["X = w"],
                                                        ["X = x"],
                                                        ["X = x"],
                                                        ["X = x"],
                                                        ["X = x"],
                                                        ["X = z"],
                                                        ["X = z"],
                                                        ["X = z"],
                                                        ["X = z"]]);
    assert_prolog_success!(&mut wam, "?- p(X, Y, X).", [["Y = h(w)", "X = f(f(s))"],
                                                        ["Y = h(x)", "X = f(f(s))"],
                                                        ["Y = h(z)", "X = f(f(s))"],
                                                        ["Y = w", "X = _0"],
                                                        ["Y = w", "X = _0"],
                                                        ["Y = w", "X = _0"],
                                                        ["Y = w", "X = _0"],
                                                        ["Y = x", "X = _0"],
                                                        ["Y = x", "X = _0"],
                                                        ["Y = x", "X = _0"],
                                                        ["Y = x", "X = _0"],
                                                        ["Y = z", "X = _0"],
                                                        ["Y = z", "X = _0"],
                                                        ["Y = z", "X = _0"],
                                                        ["Y = z", "X = _0"]]);
    assert_prolog_failure!(&mut wam, "?- p(f(f(X)), h(f(X)), Y).");

    submit(&mut wam, "p(X) :- f(Y), g(Y), i(X, Y).");
    submit(&mut wam, "g(f(a)). g(f(b)). g(f(c)).");
    submit(&mut wam, "f(f(a)). f(f(b)). f(f(c)).");
    submit(&mut wam, "i(X, X).");

    assert_prolog_success!(&mut wam, "?- p(X).", [["X = f(a)"],
                                                  ["X = f(b)"],
                                                  ["X = f(c)"]]);

    submit(&mut wam, "p(X) :- f(f(Y)), g(Y, f(Y)), i(X, f(Y)).");
    submit(&mut wam, "g(Y, f(Y)) :- g(f(Y)).");

    assert_prolog_success!(&mut wam, "?- p(X).", [["X = f(a)"],
                                                  ["X = f(b)"],
                                                  ["X = f(c)"]]);
}

#[test]
fn test_queries_on_cuts() {
    let mut wam = Machine::new();

    // test shallow cuts.
    submit(&mut wam, "memberchk(X, [X|_]) :- !.
                      memberchk(X, [_|Xs]) :- memberchk(X, Xs).");

    assert_prolog_success!(&mut wam, "?- memberchk(X, [a,b,c]).", [["X = a"]]);
    assert_prolog_success!(&mut wam, "?- memberchk([X,X], [a,b,c,[d,e],[d,d]]).", [["X = d"]]);
    assert_prolog_success!(&mut wam, "?- memberchk([X,X], [a,b,c,[D,d],[e,e]]).", [["X = d", "D = d"]]);
    assert_prolog_failure!(&mut wam, "?- memberchk([X,X], [a,b,c,[e,d],[f,e]]).");
    assert_prolog_failure!(&mut wam, "?- memberchk([X,X,Y], [a,b,c,[e,d],[f,e]]).");
    assert_prolog_success!(&mut wam, "?- memberchk([X,X,Y], [a,b,c,[e,e,d],[f,e]]).", [["X = e", "Y = d"]]);

    // test deep cuts.
    submit(&mut wam, "commit :- a, !.");

    assert_prolog_failure!(&mut wam, "?- commit.");

    submit(&mut wam, "a.");

    assert_prolog_success!(&mut wam, "?- commit.");

    submit(&mut wam, "commit(X) :- a(X), !.");

    assert_prolog_failure!(&mut wam, "?- commit(X).");

    submit(&mut wam, "a(x).");

    assert_prolog_success!(&mut wam, "?- commit(X).", [["X = x"]]);

    submit(&mut wam, "a :- b, !, c. a :- d.");

    assert_prolog_failure!(&mut wam, "?- a.");

    submit(&mut wam, "b.");

    assert_prolog_failure!(&mut wam, "?- a.");

    submit(&mut wam, "d.");

    // we've committed to the first clause since the query on b
    // succeeds, so we expect failure here.
    assert_prolog_failure!(&mut wam, "?- a.");

    submit(&mut wam, "c.");

    assert_prolog_success!(&mut wam, "?- a.");

    submit(&mut wam, "a(X) :- b, !, c(X). a(X) :- d(X).");

    assert_prolog_failure!(&mut wam, "?- a(X).");

    submit(&mut wam, "c(c).");
    submit(&mut wam, "d(d).");

    assert_prolog_success!(&mut wam, "?- a(X).", [["X = c"]]);

    submit(&mut wam, "b.");

    assert_prolog_success!(&mut wam, "?- a(X).", [["X = c"]]);

    wam.clear();

    assert_prolog_failure!(&mut wam, "?- c(X).");

    submit(&mut wam, "a(X) :- b, c(X), !. a(X) :- d(X).");
    submit(&mut wam, "b.");

    assert_prolog_failure!(&mut wam, "?- a(X).");

    submit(&mut wam, "d(d).");

    assert_prolog_success!(&mut wam, "?- a(X).", [["X = d"]]);

    submit(&mut wam, "c(c).");

    assert_prolog_success!(&mut wam, "?- a(X).", [["X = c"]]);
}

#[test]
fn test_queries_on_lists()
{
    let mut wam = Machine::new();

    submit(&mut wam, "p([Z, W]).");

    assert_prolog_success!(&mut wam, "?- p([Z, Z]).", [["Z = _0"]]);
    assert_prolog_failure!(&mut wam, "?- p([Z, W, Y]).");
    assert_prolog_success!(&mut wam, "?- p([Z | W]).", [["Z = _0", "W = [_3]"]]);
    assert_prolog_success!(&mut wam, "?- p([Z | [Z]]).", [["Z = _0"]]);
    assert_prolog_success!(&mut wam, "?- p([Z | [W]]).", [["Z = _2", "W = _0"]]);
    assert_prolog_failure!(&mut wam, "?- p([Z | []]).");

    submit(&mut wam, "p([Z, Z]).");

    assert_prolog_success!(&mut wam, "?- p([Z, Z]).", [["Z = _0"]]);
    assert_prolog_failure!(&mut wam, "?- p([Z, W, Y]).");
    assert_prolog_success!(&mut wam, "?- p([Z | W]).", [["Z = _0", "W = [_0]"]]);
    assert_prolog_success!(&mut wam, "?- p([Z | [Z]]).", [["Z = _0"]]);
    assert_prolog_success!(&mut wam, "?- p([Z | [W]]).", [["Z = _2", "W = _2"]]);
    assert_prolog_failure!(&mut wam, "?- p([Z | []]).");

    submit(&mut wam, "p([Z]).");

    assert_prolog_failure!(&mut wam, "?- p([Z, Z]).");
    assert_prolog_failure!(&mut wam, "?- p([Z, W, Y]).");
    assert_prolog_success!(&mut wam, "?- p([Z | W]).", [["W = []", "Z = _0"]]);
    assert_prolog_failure!(&mut wam, "?- p([Z | [Z]]).");
    assert_prolog_failure!(&mut wam, "?- p([Z | [W]]).");
    assert_prolog_success!(&mut wam, "?- p([Z | []]).", [["Z = _0"]]);

    submit(&mut wam, "member(X, [X|_]).
                      member(X, [_|Xs]) :- member(X, Xs).");

    assert_prolog_failure!(&mut wam, "?- member(a, [c, [X, Y]]).");
    assert_prolog_failure!(&mut wam, "?- member(c, [a, [X, Y]]).");
    assert_prolog_success!(&mut wam, "?- member(a, [a, [X, Y]]).", [["X = _2", "Y = _0"]]);

    assert_prolog_success!(&mut wam, "?- member(a, [X, Y, Z]).", [["Y = _2", "X = a",  "Z = _0"],
                                                                  ["Y = a",  "X = _4", "Z = _0"],
                                                                  ["Y = _2",  "X = _4", "Z = a"]]);

    assert_prolog_success!(&mut wam, "?- member([X, X], [a, [X, Y]]).", [["X = _0", "Y = _0"]]);
    assert_prolog_success!(&mut wam, "?- member([X, X], [a, [b, c], [b, b], [Z, x], [d, f]]).",
                           [["Z = _14", "X = b"],
                            ["Z = x",   "X = x"]]);
    assert_prolog_failure!(&mut wam, "?- member([X, X], [a, [b, c], [b, d], [foo, x], [d, f]]).");
    assert_prolog_success!(&mut wam, "?- member([X, Y], [a, [b, c], [b, b], [Z, x], [d, f]]).",
                           [["X = b", "Y = c", "Z = _14"],
                            ["X = b", "Y = b", "Z = _14"],
                            ["X = _14", "Y = x", "Z = _14"],
                            ["X = d", "Y = f", "Z = _14"]]);
    assert_prolog_failure!(&mut wam, "?- member([X, Y, Y], [a, [b, c], [b, b], [Z, x], [d, f]]).");
    assert_prolog_failure!(&mut wam, "?- member([X, Y, Z], [a, [b, c], [b, b], [Z, x], [d, f]]).");
}

#[test]
fn test_queries_on_indexed_predicates()
{
    let mut wam = Machine::new();

    submit(&mut wam, "p(a) :- a.
                      p(b) :- b, f(X).
                      p(c) :- c, g(X).
                      p(f(a)) :- a.
                      p(g(b, c)) :- b.
                      p(g(b)) :- b.
                      p([a|b]) :- a.
                      p([]).
                      p(X) :- x.
                      p([c, d, e]).");

    assert_prolog_failure!(&mut wam, "?- p(a).");
    assert_prolog_failure!(&mut wam, "?- p(b).");
    assert_prolog_failure!(&mut wam, "?- p(c).");
    assert_prolog_failure!(&mut wam, "?- p(f(a)).");
    assert_prolog_failure!(&mut wam, "?- p(g(b, X)).");
    assert_prolog_failure!(&mut wam, "?- p(g(Y, X)).");
    assert_prolog_failure!(&mut wam, "?- p(g(Y, c)).");
    assert_prolog_failure!(&mut wam, "?- p(g(b)).");
    assert_prolog_success!(&mut wam, "?- p([]).");
    assert_prolog_success!(&mut wam, "?- p([c, d, e]).");
    assert_prolog_success!(&mut wam, "?- p([c, d | X]).", [["X = [e]"]]);
    assert_prolog_success!(&mut wam, "?- p([c|X]).", [["X = [d, e]"]]);
    assert_prolog_success!(&mut wam, "?- p([Y|X]).", [["Y = c", "X = [d, e]"]]);
    assert_prolog_success!(&mut wam, "?- p([Y|[d|Xs]]).", [["Xs = [e]", "Y = c"]]);

    submit(&mut wam, "a.");

    assert_prolog_success!(&mut wam, "?- p(a).");
    assert_prolog_failure!(&mut wam, "?- p(b).");
    assert_prolog_failure!(&mut wam, "?- p(c).");
    assert_prolog_success!(&mut wam, "?- p(f(a)).");
    assert_prolog_failure!(&mut wam, "?- p(g(b, X)).");
    assert_prolog_failure!(&mut wam, "?- p(g(Y, X)).");
    assert_prolog_failure!(&mut wam, "?- p(g(Y, c)).");
    assert_prolog_failure!(&mut wam, "?- p(g(b)).");
    assert_prolog_success!(&mut wam, "?- p([]).");
    assert_prolog_success!(&mut wam, "?- p([c, d, e]).");
    assert_prolog_success!(&mut wam, "?- p([c, d | X]).", [["X = [e]"]]);
    assert_prolog_success!(&mut wam, "?- p([c|X]).", [["X = [d, e]"]]);
    assert_prolog_success!(&mut wam, "?- p([Y|X]).", [["X = b", "Y = a"],
                                                      ["Y = c", "X = [d, e]"]]);
    assert_prolog_success!(&mut wam, "?- p([Y|[d|Xs]]).", [["Xs = [e]", "Y = c"]]);

    submit(&mut wam, "b.");
    submit(&mut wam, "f(x).");

    assert_prolog_success!(&mut wam, "?- p(a).");
    assert_prolog_success!(&mut wam, "?- p(b).");
    assert_prolog_failure!(&mut wam, "?- p(c).");
    assert_prolog_success!(&mut wam, "?- p(f(a)).");
    assert_prolog_success!(&mut wam, "?- p(g(b, X)).", [["X = c"]]);
    assert_prolog_success!(&mut wam, "?- p(g(Y, X)).", [["X = c", "Y = b"]]);
    assert_prolog_success!(&mut wam, "?- p(g(Y, c)).", [["Y = b"]]);
    assert_prolog_success!(&mut wam, "?- p(g(b)).");
    assert_prolog_success!(&mut wam, "?- p([]).");
    assert_prolog_success!(&mut wam, "?- p([c, d, e]).");
    assert_prolog_success!(&mut wam, "?- p([c, d | X]).", [["X = [e]"]]);
    assert_prolog_success!(&mut wam, "?- p([c|X]).", [["X = [d, e]"]]);
    assert_prolog_success!(&mut wam, "?- p([Y|X]).", [["X = b", "Y = a"],
                                                      ["Y = c", "X = [d, e]"]]);
    assert_prolog_success!(&mut wam, "?- p([Y|[d|Xs]]).", [["Xs = [e]", "Y = c"]]);

    submit(&mut wam, "c.");
    submit(&mut wam, "g(X).");

    assert_prolog_success!(&mut wam, "?- p(a).");
    assert_prolog_success!(&mut wam, "?- p(b).");
    assert_prolog_success!(&mut wam, "?- p(c).");
    assert_prolog_success!(&mut wam, "?- p(f(a)).");
    assert_prolog_success!(&mut wam, "?- p(g(b, X)).", [["X = c"]]);
    assert_prolog_success!(&mut wam, "?- p(g(Y, X)).", [["X = c", "Y = b"]]);
    assert_prolog_success!(&mut wam, "?- p(g(Y, c)).", [["Y = b"]]);
    assert_prolog_success!(&mut wam, "?- p(g(b)).");
    assert_prolog_success!(&mut wam, "?- p([]).");
    assert_prolog_success!(&mut wam, "?- p([c, d, e]).");
    assert_prolog_success!(&mut wam, "?- p([c, d | X]).", [["X = [e]"]]);
    assert_prolog_success!(&mut wam, "?- p([c|X]).", [["X = [d, e]"]]);
    assert_prolog_success!(&mut wam, "?- p([Y|X]).", [["X = b", "Y = a"],
                                                      ["Y = c", "X = [d, e]"]]);
    assert_prolog_success!(&mut wam, "?- p([Y|[d|Xs]]).", [["Xs = [e]", "Y = c"]]);
    assert_prolog_failure!(&mut wam, "?- p(blah).");

    submit(&mut wam, "x.");

    assert_prolog_success!(&mut wam, "?- p(a).");
    assert_prolog_success!(&mut wam, "?- p(b).");
    assert_prolog_success!(&mut wam, "?- p(c).");
    assert_prolog_success!(&mut wam, "?- p(true(a)).");

    assert_prolog_success!(&mut wam, "?- p(g(b, X)).", [["X = c"],
                                                        ["X = _2"]]);
    assert_prolog_success!(&mut wam, "?- p(g(Y, X)).", [["X = c", "Y = b"],
                                                        ["X = _2", "Y = _1"]]);
    assert_prolog_success!(&mut wam, "?- p(g(Y, c)).", [["Y = b"],
                                                        ["Y = _1"]]);

    assert_prolog_success!(&mut wam, "?- p(g(b)).");
    assert_prolog_success!(&mut wam, "?- p([]).");
    assert_prolog_success!(&mut wam, "?- p([c, d, e]).");

    assert_prolog_success!(&mut wam, "?- p([c, d | X]).", [["X = _1"],
                                                           ["X = [e]"]]);
    assert_prolog_success!(&mut wam, "?- p([c|X]).", [["X = _1"],
                                                      ["X = [d, e]"]]);
    assert_prolog_success!(&mut wam, "?- p([Y|X]).", [["X = b", "Y = a"],
                                                      ["X = _1", "Y = _0"],
                                                      ["Y = c", "X = [d, e]"]]);
    assert_prolog_success!(&mut wam, "?- p([Y|[d|Xs]]).", [["Xs = _1", "Y = _2"],
                                                           ["Xs = [e]", "Y = c"]]);

    assert_prolog_success!(&mut wam, "?- p(blah).");

    submit(&mut wam, "ind_call(or(X, Y)) :- ind_call(X).
                      ind_call(trace) :- trace.
                      ind_call(or(X, Y)) :- ind_call(Y).
                      ind_call(notrace) :- notrace.
                      ind_call(nl) :- nl.
                      ind_call(X) :- builtin(X).
                      ind_call(X) :- extern(X).
                      ind_call(ind_call(X)) :- ind_call(X).
                      ind_call(repeat).
                      ind_call(repeat) :- ind_call(repeat).
                      ind_call(false).");

    assert_prolog_success!(&mut wam, "?- ind_call(repeat).");
    assert_prolog_success!(&mut wam, "?- ind_call(false).");
    assert_prolog_success!(&mut wam, "?- ind_call(ind_call(repeat)).");
    assert_prolog_success!(&mut wam, "?- ind_call(ind_call(false)).");
    assert_prolog_failure!(&mut wam, "?- ind_call(notrace).");
    assert_prolog_failure!(&mut wam, "?- ind_call(nl).");
    assert_prolog_failure!(&mut wam, "?- ind_call(builtin(X)).");
    assert_prolog_failure!(&mut wam, "?- ind_call(extern(X)).");

    submit(&mut wam, "notrace.");
    submit(&mut wam, "nl.");

    assert_prolog_success!(&mut wam, "?- ind_call(repeat).");
    assert_prolog_success!(&mut wam, "?- ind_call(false).");
    assert_prolog_success!(&mut wam, "?- ind_call(ind_call(repeat)).");
    assert_prolog_success!(&mut wam, "?- ind_call(ind_call(false)).");
    assert_prolog_success!(&mut wam, "?- ind_call(notrace).");
    assert_prolog_success!(&mut wam, "?- ind_call(nl).");
    assert_prolog_failure!(&mut wam, "?- ind_call(builtin(X)).");
    assert_prolog_failure!(&mut wam, "?- ind_call(extern(X)).");

    submit(&mut wam, "builtin(X).");
    submit(&mut wam, "extern(x).");

    assert_prolog_success!(&mut wam, "?- ind_call(repeat).");
    assert_prolog_success!(&mut wam, "?- ind_call(false).");
    assert_prolog_success!(&mut wam, "?- ind_call(ind_call(repeat)).");
    assert_prolog_success!(&mut wam, "?- ind_call(ind_call(false)).");
    assert_prolog_success!(&mut wam, "?- ind_call(notrace).");
    assert_prolog_success!(&mut wam, "?- ind_call(nl).");
    assert_prolog_success!(&mut wam, "?- ind_call(builtin(X)).", [["X = _1"]]);
    assert_prolog_success!(&mut wam, "?- ind_call(extern(X)).", [["X = _1"]]);
}

#[test]
fn test_queries_on_conjuctive_queries() {
    let mut wam = Machine::new();

    submit(&mut wam, "p(a, b).");
    submit(&mut wam, "q(b, c).");

    assert_prolog_success!(&mut wam, "?- p(X, Y), q(Y, Z).", [["X = a", "Z = c", "Y = b"]]);
    assert_prolog_failure!(&mut wam, "?- p(X, Y), q(Y, X).");

    submit(&mut wam, "p(a, [f(g(X))]).");
    submit(&mut wam, "q(Y, c).");

    assert_prolog_success!(&mut wam, "?- p(X, Y), q(Y, Z).", [["Y = [f(g(_9))]", "X = a", "Z = c"]]);
    assert_prolog_failure!(&mut wam, "?- p(X, Y), q(Y, X).");

    submit(&mut wam, "member(X, [X|_]).
                      member(X, [_|Xs]) :- member(X, Xs).");

    assert_prolog_success!(&mut wam, "?- member(X, [a,b,c]), member(X, [a,b,c]).",
                           [["X = a"],
                            ["X = b"],
                            ["X = c"]]);
    assert_prolog_success!(&mut wam, "?- member(X, [a,b,c]), member(X, [b,c]).",
                           [["X = b"],
                            ["X = c"]]);
    assert_prolog_success!(&mut wam, "?- member(X, [a,c]), member(X, [b,c]).",
                           [["X = c"]]);
    assert_prolog_success!(&mut wam, "?- member(X, [a,b,c,d]), !, member(X, [a,d]).",
                           [["X = a"]]);
    assert_prolog_failure!(&mut wam, "?- member(X, [a,b,c,d]), !, member(X, [e]).");
    assert_prolog_success!(&mut wam, "?- member([X,X],[a,b,c,[d,d],[e,d]]),
                                         member(X, [a,b,c,d,e,f,g]),
                                         member(Y, [X, a, b, c, d]).",
                           [["X = d", "Y = d"],
                            ["X = d", "Y = a"],
                            ["X = d", "Y = b"],
                            ["X = d", "Y = c"],
                            ["X = d", "Y = d"]]);

    submit(&mut wam, "p(a, [f(g(X))]). p(X, c) :- c.");
    submit(&mut wam, "c.");
    submit(&mut wam, "q(Y, c).");

    assert_prolog_success!(&mut wam, "?- p(X, Y), q(Y, Z).",
                           [["X = a",  "Z = c", "Y = [f(g(_9))]"],
                            ["X = _0", "Z = c", "Y = c"]]);
    assert_prolog_success!(&mut wam, "?- p(X, Y), !, q(Y, Z).",
                           [["Z = c", "Y = [f(g(_9))]", "X = a"]]);

    submit(&mut wam, "q([f(g(x))], Z). q([f(g(y))], Y). q([f(g(z))], a).");

    assert_prolog_success!(&mut wam, "?- p(X, Y), q(Y, Z).",
                           [["Z = _10", "X = a", "Y = [f(g(x))]"],
                            ["Z = _10", "X = a", "Y = [f(g(y))]"],
                            ["Z = a", "X = a", "Y = [f(g(z))]"]]);
    assert_prolog_success!(&mut wam, "?- p(X, Y), !, q(Y, Z).",
                           [["X = a", "Y = [f(g(x))]", "Z = _10"],
                            ["X = a", "Y = [f(g(y))]", "Z = _10"],
                            ["X = a", "Y = [f(g(z))]", "Z = a"]]);
    assert_prolog_success!(&mut wam, "?- p(X, Y), !, q(Y, X).",
                           [["X = a", "Y = [f(g(x))]"],
                            ["X = a", "Y = [f(g(y))]"],
                            ["X = a", "Y = [f(g(z))]"]]);

    submit(&mut wam, "p(X, [f(g(x))]). p(X, [f(g(y))]). p(X, [f(g(z))]).");

    assert_prolog_failure!(&mut wam, "?- q(f(X), Y), p(X, Y).");
    assert_prolog_success!(&mut wam, "?- q(X, Y), p(X, Y).",
                           [["Y = [f(g(x))]", "X = [f(g(x))]"],
                            ["Y = [f(g(y))]", "X = [f(g(x))]"],
                            ["Y = [f(g(z))]", "X = [f(g(x))]"],
                            ["Y = [f(g(x))]", "X = [f(g(y))]"],
                            ["Y = [f(g(y))]", "X = [f(g(y))]"],
                            ["Y = [f(g(z))]", "X = [f(g(y))]"]]);
    assert_prolog_success!(&mut wam, "?- p(X, Y), q(X, Y).",
                           [["Y = [f(g(x))]", "X = [f(g(x))]"],
                            ["Y = [f(g(x))]", "X = [f(g(y))]"],
                            ["Y = [f(g(y))]", "X = [f(g(x))]"],
                            ["Y = [f(g(y))]", "X = [f(g(y))]"],
                            ["Y = [f(g(z))]", "X = [f(g(x))]"],
                            ["Y = [f(g(z))]", "X = [f(g(y))]"]]);
    assert_prolog_success!(&mut wam, "?- p(X, Y), q(Y, X).",
                           [["Y = [f(g(x))]", "X = s_0_2"],
                            ["Y = [f(g(y))]", "X = s_0_2"],
                            ["Y = [f(g(z))]", "X = a"]]);
    assert_prolog_success!(&mut wam, "?- q(X, Y), p(Y, X).",
                           [["Y = s_0_1", "X = [f(g(x))]"],
                            ["Y = s_0_1", "X = [f(g(y))]"],
                            ["Y = a"    , "X = [f(g(z))]"]]);
}

#[test]
fn test_queries_on_call_n()
{
    let mut wam = Machine::new();

    submit(&mut wam, "maplist(_, []).
                      maplist(P, [X|Xs]) :- call(P, X), maplist(P, Xs).");
    submit(&mut wam, "f(a). f(b). f(c).");

    assert_prolog_success!(&mut wam, "?- maplist(f, [X,Y,Z]).",
                           [["X = a", "Y = a", "Z = a"],
                            ["X = a", "Y = a", "Z = b"],
                            ["X = a", "Y = a", "Z = c"],
                            ["X = a", "Y = b", "Z = a"],
                            ["X = a", "Y = b", "Z = b"],
                            ["X = a", "Y = b", "Z = c"],
                            ["X = a", "Y = c", "Z = a"],
                            ["X = a", "Y = c", "Z = b"],
                            ["X = a", "Y = c", "Z = c"],
                            ["X = b", "Y = a", "Z = a"],
                            ["X = b", "Y = a", "Z = b"],
                            ["X = b", "Y = a", "Z = c"],
                            ["X = b", "Y = b", "Z = a"],
                            ["X = b", "Y = b", "Z = b"],
                            ["X = b", "Y = b", "Z = c"],
                            ["X = b", "Y = c", "Z = a"],
                            ["X = b", "Y = c", "Z = b"],
                            ["X = b", "Y = c", "Z = c"],
                            ["X = c", "Y = a", "Z = a"],
                            ["X = c", "Y = a", "Z = b"],
                            ["X = c", "Y = a", "Z = c"],
                            ["X = c", "Y = b", "Z = a"],
                            ["X = c", "Y = b", "Z = b"],
                            ["X = c", "Y = b", "Z = c"],
                            ["X = c", "Y = c", "Z = a"],
                            ["X = c", "Y = c", "Z = b"],
                            ["X = c", "Y = c", "Z = c"]]);

    assert_prolog_success!(&mut wam, "?- maplist(f, [a,Y,Z]).",
                           [["Y = a", "Z = a"],
                            ["Y = a", "Z = b"],
                            ["Y = a", "Z = c"],
                            ["Y = b", "Z = a"],
                            ["Y = b", "Z = b"],
                            ["Y = b", "Z = c"],
                            ["Y = c", "Z = a"],
                            ["Y = c", "Z = b"],
                            ["Y = c", "Z = c"]]);

    assert_prolog_success!(&mut wam, "?- maplist(f, [X,a,b]).",
                           [["X = a"],
                            ["X = b"],
                            ["X = c"]]);
    assert_prolog_success!(&mut wam, "?- maplist(f, [c,a,b]).");
    assert_prolog_failure!(&mut wam, "?- maplist(f, [d,e,f]).");
    assert_prolog_success!(&mut wam, "?- maplist(f, []).");
    assert_prolog_failure!(&mut wam, "?- maplist(f(X), [a,b,c]).");

    submit(&mut wam, "f(X) :- call(X), call(X).");
    submit(&mut wam, "p(x). p(y).");

    assert_prolog_failure!(&mut wam, "?- f(p).");
    assert_prolog_success!(&mut wam, "?- f(p(X)).", [["X = x"],
                                                     ["X = y"]]);
    assert_prolog_success!(&mut wam, "?- f(p(x)).");
    assert_prolog_failure!(&mut wam, "?- f(p(w)).");
    assert_prolog_failure!(&mut wam, "?- f(p(X, Y)).");

    submit(&mut wam, "f(P) :- call(P, X), call(P, Y).");

    assert_prolog_success!(&mut wam, "?- f(p).");
    assert_prolog_failure!(&mut wam, "?- f(non_existent).");

    submit(&mut wam, "f(P, X, Y) :- call(P, X), call(P, Y).");

    assert_prolog_success!(&mut wam, "?- f(p, X, Y).", [["Y = x", "X = x"],
                                                        ["Y = y", "X = x"],
                                                        ["Y = x", "X = y"],
                                                        ["Y = y", "X = y"]]);
    assert_prolog_success!(&mut wam, "?- f(p, x, Y).", [["Y = x"],
                                                        ["Y = y"]]);
    assert_prolog_success!(&mut wam, "?- f(p, X, y).", [["X = x"],
                                                        ["X = y"]]);
    assert_prolog_success!(&mut wam, "?- f(p, x, y).");
    assert_prolog_failure!(&mut wam, "?- f(p, X, z).");
    assert_prolog_failure!(&mut wam, "?- f(p, z, Y).");

    assert_prolog_success!(&mut wam, "?- call(p, X).", [["X = x"],
                                                        ["X = y"]]);
    assert_prolog_success!(&mut wam, "?- call(p, x).");
    assert_prolog_success!(&mut wam, "?- call(p, y).");
    assert_prolog_failure!(&mut wam, "?- call(p, z).");

    submit(&mut wam, "r(f(X)) :- p(X). r(g(Y)) :- p(Y).");

    assert_prolog_success!(&mut wam, "?- f(r, X, Y).",
                           [["X = f(x)", "Y = f(x)"],
                            ["X = f(x)", "Y = f(y)"],
                            ["X = f(x)", "Y = g(x)"],
                            ["X = f(x)", "Y = g(y)"],
                            ["X = f(y)", "Y = f(x)"],
                            ["X = f(y)", "Y = f(y)"],
                            ["X = f(y)", "Y = g(x)"],
                            ["X = f(y)", "Y = g(y)"],
                            ["X = g(x)", "Y = f(x)"],
                            ["X = g(x)", "Y = f(y)"],
                            ["X = g(x)", "Y = g(x)"],
                            ["X = g(x)", "Y = g(y)"],
                            ["X = g(y)", "Y = f(x)"],
                            ["X = g(y)", "Y = f(y)"],
                            ["X = g(y)", "Y = g(x)"],
                            ["X = g(y)", "Y = g(y)"]]);
    assert_prolog_success!(&mut wam, "?- f(r, X, X).",
                           [["X = f(x)"],
                            ["X = f(y)"],
                            ["X = g(x)"],
                            ["X = g(y)"]]);
    assert_prolog_success!(&mut wam, "?- f(r, f(X), g(Y)).",
                           [["X = x", "Y = x"],
                            ["X = x", "Y = y"],
                            ["X = y", "Y = x"],
                            ["X = y", "Y = y"]]);
    assert_prolog_failure!(&mut wam, "?- f(r, j(X), h(Y)).");

    submit(&mut wam, "p(one, one). p(one, two). p(two, two).");

    assert_prolog_success!(&mut wam, "?- f(p(one), X, Y).",
                           [["X = one", "Y = one"],
                            ["X = one", "Y = two"],
                            ["X = two", "Y = one"],
                            ["X = two", "Y = two"]]);
    assert_prolog_success!(&mut wam, "?- f(p(one), X, X).",
                           [["X = one"],
                            ["X = two"]]);
    assert_prolog_success!(&mut wam, "?- f(p(one), one, Y).",
                           [["Y = one"],
                            ["Y = two"]]);
    assert_prolog_success!(&mut wam, "?- f(p(one), one, two).");
    assert_prolog_failure!(&mut wam, "?- f(p(one), one, three).");

    assert_prolog_failure!(&mut wam, "?- f(p(two), one, two).");
    assert_prolog_failure!(&mut wam, "?- f(p(two), two, one).");
    assert_prolog_success!(&mut wam, "?- f(p(two), two, two).");
    assert_prolog_failure!(&mut wam, "?- f(p(two), two, three).");

    assert_prolog_failure!(&mut wam, "?- f(p(three), X, Y).");
    assert_prolog_failure!(&mut wam, "?- f(p(three), X, X).");
    assert_prolog_failure!(&mut wam, "?- f(p(three), one, Y).");
    assert_prolog_failure!(&mut wam, "?- f(p(three), one, two).");
    assert_prolog_failure!(&mut wam, "?- f(p(three), one, three).");

    submit(&mut wam, "f(P, X) :- call(P, X).");

    assert_prolog_success!(&mut wam, "?- f(p(one), one).");
    assert_prolog_success!(&mut wam, "?- f(p(two), two).");
    assert_prolog_failure!(&mut wam, "?- f(p(two), one).");
    assert_prolog_failure!(&mut wam, "?- f(p(three), one).");
    assert_prolog_failure!(&mut wam, "?- f(p(one), three).");
    assert_prolog_failure!(&mut wam, "?- f(p(two), three).");

    submit(&mut wam, "p(f(g(X)), compound, [lists,are,good]).");

    assert_prolog_success!(&mut wam, "?- call(p(f(g(X))), Y, Z).",
                           [["Y = compound", "Z = [lists, are, good]", "X = _3"]]);

    submit(&mut wam, "david_lynch(coffee).
                      david_lynch(pie).
                      david_lynch(kyle(Film)) :- kyle(Film).");

    submit(&mut wam, "kyle(dune).
                      kyle(blue_velvet).
                      kyle(showgirls).
                      kyle(flintstones).");

    assert_prolog_success!(&mut wam, "?- call(david_lynch, X).",
                           [["X = coffee"],
                            ["X = pie"],
                            ["X = kyle(dune)"],
                            ["X = kyle(blue_velvet)"],
                            ["X = kyle(showgirls)"],
                            ["X = kyle(flintstones)"]]);
    assert_prolog_success!(&mut wam, "?- call(david_lynch, kyle(Film)).",
                           [["Film = dune"],
                            ["Film = blue_velvet"],
                            ["Film = showgirls"],
                            ["Film = flintstones"]]);
    assert_prolog_failure!(&mut wam, "?- call(david_lynch, kyle(Film), _).");

    submit(&mut wam, "call_mult(P, X) :- call(call(P), X).");

    assert_prolog_success!(&mut wam, "?- call_mult(p(X), Y).",
                           [["Y = one", "X = one"],
                            ["Y = two", "X = one"],
                            ["Y = two", "X = two"]]);
    assert_prolog_success!(&mut wam, "?- call_mult(p(X), X).",
                           [["X = one"],
                            ["X = two"]]);
    assert_prolog_success!(&mut wam, "?- call_mult(p(one), X).",
                           [["X = one"],
                            ["X = two"]]);
    assert_prolog_success!(&mut wam, "?- call_mult(p(X), one).",
                           [["X = one"]]);

    assert_prolog_failure!(&mut wam, "?- call_mult(p(two), one).");
    assert_prolog_success!(&mut wam, "?- call_mult(p(two), two).");

    assert_prolog_success!(&mut wam, "?- call(call(p(one)), X), call(call(p(two)), two).",
                           [["X = one"],
                            ["X = two"]]);
    assert_prolog_success!(&mut wam, "?- call(call(p(one, X))), call(call(p(two, two))).",
                           [["X = one"],
                            ["X = two"]]);
    assert_prolog_failure!(&mut wam, "?- call(call(p(one)), X), call(call(p(two)), one).");
    assert_prolog_success!(&mut wam, "?- call(call(p(X)), X), call(call(p(Y)), Y).",
                           [["X = one", "Y = one"],
                            ["X = one", "Y = two"],
                            ["X = two", "Y = one"],
                            ["X = two", "Y = two"]]);
    assert_prolog_success!(&mut wam, "?- call(call(p(X)), Y), call(call(p(Y)), X).",
                           [["X = one", "Y = one"],
                            ["X = two", "Y = two"]]);
    assert_prolog_success!(&mut wam, "?- call(call(p), X, Y), call(call(call(p)), X, Y).",
                           [["X = one", "Y = one"],
                            ["Y = two", "X = one"],
                            ["Y = two", "X = two"]]);
    assert_prolog_success!(&mut wam, "?- call(call(p), X, Y), call(call(call(p(X))), Y).",
                           [["X = one", "Y = one"],
                            ["Y = two", "X = one"],
                            ["Y = two", "X = two"]]);
    assert_prolog_failure!(&mut wam, "?- call(call(p), X, Y), call(call(call(p(X))), X, Y).");
    assert_prolog_success!(&mut wam, "?- call(call(p), X, Y), call(call(call(p(X))), X).",
                           [["X = one", "Y = one"],
                            ["Y = two", "X = one"],
                            ["Y = two", "X = two"]]);

    submit(&mut wam, "f(call(f, undefined)). f(undefined).");
    submit(&mut wam, "call_var(P) :- P.");

    assert_prolog_success!(&mut wam, "?- f(X), call_var(X).",
                           [["X = call(f, undefined)"]]);
    assert_prolog_success!(&mut wam, "?- f(call(f, Q)), call_var(call(f, Q)).",
                           [["Q = undefined"]]);
    assert_prolog_failure!(&mut wam, "?- call_var(call(undefined, Q)).");

    assert_prolog_failure!(&mut wam, "?- call(call).");
    assert_prolog_failure!(&mut wam, "?- call(call(call)).");
    assert_prolog_failure!(&mut wam, "?- call(call(call(call))).");
    assert_prolog_failure!(&mut wam, "?- call(call(call(call(call)))).");
    assert_prolog_failure!(&mut wam, "?- call(call(call(call(call(call))))).");
    assert_prolog_success!(&mut wam, "?- call(call(call(call(call(call(p(X))))))).",
                           [["X = x"],
                            ["X = y"]]);
}

#[test]
fn test_queries_on_exceptions()
{
    let mut wam = Machine::new();

    submit(&mut wam, "f(a). f(_) :- throw(stuff).");
    submit(&mut wam, "handle(stuff).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), E, handle(E)).",
                           [["E = _2", "X = a"],
                            ["E = stuff", "X = _1"]]);

    submit(&mut wam, "f(a). f(X) :- g(X).");
    submit(&mut wam, "g(x). g(y). g(z).");
    submit(&mut wam, "handle(x). handle(y).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), X, handle(X)).",
                           [["X = a"],
                            ["X = x"],
                            ["X = y"],
                            ["X = z"]]);
    assert_prolog_success!(&mut wam, "?- catch(f(a), _, handle(X)).",
                           [["X = _4"]]);
    assert_prolog_failure!(&mut wam, "?- catch(f(b), _, handle(X)).");

    submit(&mut wam, "g(x). g(X) :- throw(x).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), x, handle(X)).",
                           [["X = a"],
                            ["X = x"],
                            ["X = x"],
                            ["X = y"]]);
    assert_prolog_success!(&mut wam, "?- catch(f(X), x, handle(z)).",
                           [["X = a"],
                            ["X = x"]]);
    assert_prolog_success!(&mut wam, "?- catch(f(z), x, handle(x)).");
    assert_prolog_success!(&mut wam, "?- catch(f(z), x, handle(y)).");
    assert_prolog_failure!(&mut wam, "?- catch(f(z), x, handle(z)).");

    submit(&mut wam, "f(X) :- throw(stuff).");
    submit(&mut wam, "handle(stuff). handle(other_stuff).");

    // the first 3 cases should deterministically succeed.
    assert_prolog_success!(&mut wam, "?- catch(f(X), E, handle(E)).",
                           [["X = _1", "E = stuff"]]);
    assert_prolog_success!(&mut wam, "?- catch(f(X), E, handle(stuff)).",
                           [["X = _1", "E = stuff"]]);
    assert_prolog_success!(&mut wam, "?- catch(f(X), E, handle(other_stuff)).",
                           [["X = _1", "E = stuff"]]);
    assert_prolog_failure!(&mut wam, "?- catch(f(X), E, handle(not_stuff)).");

    submit(&mut wam, "f(success). f(X) :- catch(g(X), E, handle(E)).");
    submit(&mut wam, "g(g_success). g(g_success_2). g(X) :- throw(X).");
    submit(&mut wam, "handle(x). handle(y). handle(z).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), E, E).",
                           [["X = success", "E = _2"],
                            ["X = g_success", "E = _2"],
                            ["X = g_success_2", "E = _2"],
                            ["X = _1", "E = _2"],
                            ["X = _1", "E = _2"],
                            ["X = _1", "E = _2"]]);
    assert_prolog_failure!(&mut wam, "?- catch(f(fail), _, _).");
    assert_prolog_success!(&mut wam, "?- catch(f(x), _, _).");
    assert_prolog_success!(&mut wam, "?- catch(f(y), _, _).");
    assert_prolog_success!(&mut wam, "?- catch(f(z), _, _).");

    submit(&mut wam, "f(success). f(E) :- catch(g(E), E, handle(E)).");
    submit(&mut wam, "g(g_success). g(g_success_2). g(X) :- throw(X).");
    submit(&mut wam, "handle(x). handle(y). handle(z). handle(v) :- throw(X).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), E, E).",
                           [["X = success", "E = _2"],
                            ["X = g_success", "E = _2"],
                            ["X = g_success_2", "E = _2"],
                            ["X = x", "E = _2"],
                            ["X = y", "E = _2"],
                            ["X = z", "E = _2"]]);

    submit(&mut wam, "handle(x). handle(y). handle(z). handle(v) :- throw(handle_top(X)).");
    submit(&mut wam, "handle_top(an_error_1). handle_top(an_error_2).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), E, E).",
                           [["X = success", "E = _2"],
                            ["X = g_success", "E = _2"],
                            ["X = g_success_2", "E = _2"],
                            ["X = x", "E = _2"],
                            ["X = y", "E = _2"],
                            ["X = z", "E = _2"],
                            ["X = _1", "E = handle_top(an_error_1)"],
                            ["X = _1", "E = handle_top(an_error_2)"]]);

    submit(&mut wam, "handle(x). handle(y). handle(z). handle(v) :- throw(X).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), E, handle_top(E)).",
                           [["X = success", "E = _2"],
                            ["X = g_success", "E = _2"],
                            ["X = g_success_2", "E = _2"],
                            ["X = x", "E = _2"],
                            ["X = y", "E = _2"],
                            ["X = z", "E = _2"],
                            ["E = an_error_1", "X = _1"],
                            ["E = an_error_2", "X = _1"]]);
}

#[test]
fn test_queries_on_arithmetic()
{
    let mut wam = Machine::new();

    assert_prolog_success!(&mut wam, "?- X is 1, X is X.", [["X = 1"]]);
    assert_prolog_failure!(&mut wam, "?- X is 1, X is X + 1.");
    assert_prolog_success!(&mut wam, "?- X is 1, X is X + 0.", [["X = 1"]]);
    assert_prolog_success!(&mut wam, "?- X is 1, X is X * 1.", [["X = 1"]]);
    assert_prolog_failure!(&mut wam, "?- X is 1, X is X * 2.");

    assert_prolog_failure!(&mut wam, "?- X is 1 + a.");
    assert_prolog_failure!(&mut wam, "?- X is 1 + Y.");
    assert_prolog_success!(&mut wam, "?- Y is 2 + 2 - 2, X is 1 + Y, X = 3.",
                           [["X = 3", "Y = 2"]]);
    assert_prolog_failure!(&mut wam, "?- Y is 2 + 2 - 2, X is 1 + Y, X = 2.");

    assert_prolog_success!(&mut wam, "?- 6 is 6.");
    assert_prolog_success!(&mut wam, "?- 6 is 3 + 3.");
    assert_prolog_success!(&mut wam, "?- 6 is 3 * 2.");
    assert_prolog_failure!(&mut wam, "?- 7 is 3 * 2.");
    assert_prolog_failure!(&mut wam, "?- 7 is 3.5 * 2.");
    assert_prolog_success!(&mut wam, "?- 7.0 is 3.5 * 2.");
    assert_prolog_success!(&mut wam, "?- 7.0 is 14 / 2.");
    assert_prolog_failure!(&mut wam, "?- 4.666 is 14.0 / 3.");
    assert_prolog_success!(&mut wam, "?- 4.0 is 8.0 / 2.");

    submit(&mut wam, "f(X) :- X is 5 // 0.");

    assert_prolog_success!(&mut wam, "?- catch(f(X), evaluation_error(E), true), E = zero_divisor.",
                           [["E = zero_divisor", "X = _1"]]);

    submit(&mut wam, "f(X) :- X is (5 rdiv 1) / 0.");

    assert_prolog_success!(&mut wam, "?- catch(f(X), evaluation_error(E), true), E = zero_divisor.",
                           [["E = zero_divisor", "X = _1"]]);

    submit(&mut wam, "f(X) :- X is 5.0 / 0.");

    assert_prolog_success!(&mut wam, "?- catch(f(X), evaluation_error(E), true), E = zero_divisor.",
                           [["E = zero_divisor", "X = _1"]]);

    assert_prolog_success!(&mut wam, "?- X is ((3 + 4) // 2) + 2 - 1 // 1, Y is 2+2, Z is X+Y.",
                           [["Y = 4", "X = 4", "Z = 8"]]);

    assert_prolog_success!(&mut wam, "?- X is ((3 + 4) // 2) + 2 - 1 // 1, Y is 2+2, Z = 8, Y is 4.",
                           [["Y = 4", "X = 4", "Z = 8"]]);

    assert_prolog_success!(&mut wam, "?- X is (3 rdiv 4) / 2, Y is 3 rdiv 8, X = Y.",
                           [["X = 3/8", "Y = 3/8"]]);

    assert_prolog_success!(&mut wam, "?- X is 10 xor -4, X is -10.", [["X = -10"]]);
    assert_prolog_success!(&mut wam, "?- X is 4 xor -7, X is -3.", [["X = -3"]]);
    assert_prolog_success!(&mut wam, "?- X is 10 xor 5 + 55, X = 70.", [["X = 70"]]);

    assert_prolog_success!(&mut wam, "?- X is 10 rem -3, X = 1.",   [["X = 1"]]);
    assert_prolog_success!(&mut wam, "?- X is 10 mod -3, X is -2.", [["X = -2"]]);

    assert_prolog_success!(&mut wam, "?- call(is, X, 3 + 4).", [["X = 7"]]);

    assert_prolog_success!(&mut wam, "?- Y is 3 + 3, call(is, X, Y + 4).", [["Y = 6", "X = 10"]]);
    assert_prolog_success!(&mut wam, "?- call(is, X, 3 + 4.5).", [["X = 7.5"]]);
    assert_prolog_success!(&mut wam, "?- X is 2 rdiv 3, call(is, Y, X*X).", [["X = 2/3", "Y = 4/9"]]);

    assert_prolog_failure!(&mut wam, "?- call(>, 3, 3 + 3).");
    assert_prolog_failure!(&mut wam, "?- X is 3 + 3, call(>, 3, X).");

    assert_prolog_success!(&mut wam, "?- X is 3 + 3, call(<, 3, X).", [["X = 6"]]);
    assert_prolog_success!(&mut wam, "?- X is 3 + 3, X =:= 3 + 3.", [["X = 6"]]);

    assert_prolog_success!(&mut wam, "?- catch(call(is, X, 3 // 0), E, true).",
                           [["X = _5", "E = evaluation_error(zero_divisor)"]]);

    assert_prolog_success!(&mut wam, "?- catch(call(is, X, 3 // 3), _, true).", [["X = 1"]]);

    submit(&mut wam, "f(X, Sum) :- ( integer(X) -> Sum is X + X * X + 3 ;
                                     var(X) -> Sum = 1, X = 1 ).");

    assert_prolog_success!(&mut wam, "?- f(X, Sum).", [["X = 1", "Sum = 1"]]);
    assert_prolog_success!(&mut wam, "?- f(5, Sum).", [["Sum = 33"]]);
    assert_prolog_success!(&mut wam, "?- f(5, 33).");
    assert_prolog_failure!(&mut wam, "?- f(5, 32).");
}

#[test]
fn test_queries_on_conditionals()
{
    let mut wam = Machine::new();

    submit(&mut wam, "test(A) :- (   A =:= 2 ->
                                     display(\"A is 2\")
                                 ;   A =:= 3 ->
                                     display(\"A is 3\")
                                 ;   A = \"not 2 or 3\"
                                 ).");

    assert_prolog_success!(&mut wam, "?- catch(test(A), instantiation_error(_), true).");
    assert_prolog_success!(&mut wam, "?- A = 2, test(A).", [["A = 2"]]);
    assert_prolog_success!(&mut wam, "?- A = 3, test(A), B = 3, test(B).", [["A = 3", "B = 3"]]);

    submit(&mut wam, "f(a). f(b).");
    submit(&mut wam, "g(1). g(2). g(3).");

    submit(&mut wam, "typed_dispatch(X) :- ( var(X) -> f(X)
                                           ; integer(X) -> g(X)
                                           ; atomic(X)).");

    assert_prolog_success!(&mut wam, "?- typed_dispatch(X).", [["X = a"], ["X = b"]]);
    assert_prolog_success!(&mut wam, "?- typed_dispatch(a).");
    assert_prolog_success!(&mut wam, "?- typed_dispatch(b).");
    assert_prolog_success!(&mut wam, "?- typed_dispatch(c).");
    assert_prolog_success!(&mut wam, "?- typed_dispatch(1).");
    assert_prolog_success!(&mut wam, "?- typed_dispatch(2).");
    assert_prolog_success!(&mut wam, "?- typed_dispatch(3).");
    assert_prolog_failure!(&mut wam, "?- typed_dispatch(4).");
    assert_prolog_failure!(&mut wam, "?- typed_dispatch(5).");
    assert_prolog_failure!(&mut wam, "?- typed_dispatch(compound(term)).");

    submit(&mut wam, "f(a). f(b). f(compound(term)).");
    submit(&mut wam, "g(X, Y) :- f(X), (atomic(X) -> X = a ; X = a ; X = compound(Y)).");

    assert_prolog_success!(&mut wam, "?- g(X, Y).",
                           [["Y = _1", "X = a"],
                            ["Y = term", "X = compound(term)"]]);

    assert_prolog_success!(&mut wam, "?- g(X, X).", [["X = a"]]);
    assert_prolog_success!(&mut wam, "?- g(compound(X), X).", [["X = term"]]);
    assert_prolog_success!(&mut wam, "?- g(X, term).", [["X = a"], ["X = compound(term)"]]);
    assert_prolog_success!(&mut wam, "?- g(a, _).");
    assert_prolog_success!(&mut wam, "?- g(X, _), X = a.", [["X = a"]]);

    submit(&mut wam, "g(X) :- var(X) -> (var(X) -> X is 3 + 3 ; X = not_6).");

    assert_prolog_success!(&mut wam, "?- g(X).", [["X = 6"]]);
    assert_prolog_failure!(&mut wam, "?- g(1).");
    assert_prolog_failure!(&mut wam, "?- g(6).");
    assert_prolog_failure!(&mut wam, "?- g(not_6).");

    assert_prolog_success!(&mut wam, "?- f(X), (g(Y), !).", [["X = a", "Y = 6"]]);

    submit(&mut wam, "test(X, [X]) :- (atomic(X) -> true ; throw(type_error(atomic_expected, X))).
                      test(_, _).");

    assert_prolog_success!(&mut wam, "?- catch(test(a, [a]), type_error(E), true).",
                           [["E = _6"], ["E = _6"]]);

    //TODO: write tests for calling ;, ->, to confirm behavior is correct.
    assert_prolog_success!(&mut wam, "?- f(X), call(->, atomic(X), true).",
                           [["X = a"], ["X = b"]]);
}

#[test]
fn test_queries_on_builtins()
{
    let mut wam = Machine::new();

    assert_prolog_failure!(&mut wam, "?- atomic(X).");
    assert_prolog_success!(&mut wam, "?- atomic(a).");
    assert_prolog_success!(&mut wam, "?- atomic(\"string\").");
    assert_prolog_success!(&mut wam, "?- atomic([]).");
    assert_prolog_success!(&mut wam, "?- atomic(1).");
    assert_prolog_success!(&mut wam, "?- atomic(0).");
    assert_prolog_success!(&mut wam, "?- atomic(0.0).");
    assert_prolog_failure!(&mut wam, "?- atomic([a,b,c]).");
    assert_prolog_failure!(&mut wam, "?- atomic(atop(the_trees)).");

    assert_prolog_success!(&mut wam, "?- var(X), X = 3, atomic(X).", [["X = 3"]]);
    assert_prolog_failure!(&mut wam, "?- var(X), X = 3, var(X).");

    assert_prolog_success!(&mut wam, "?- arg(N, f(a,b,c,d), Arg).",
                           [["N = 1", "Arg = a"],
                            ["N = 2", "Arg = b"],
                            ["N = 3", "Arg = c"],
                            ["N = 4", "Arg = d"]]);

    assert_prolog_success!(&mut wam, "?- arg(1, f(a,b,c,d), Arg).", [["Arg = a"]]);
    assert_prolog_success!(&mut wam, "?- arg(2, f(a,b,c,d), Arg).", [["Arg = b"]]);
    assert_prolog_success!(&mut wam, "?- arg(3, f(a,b,c,d), Arg).", [["Arg = c"]]);
    assert_prolog_success!(&mut wam, "?- arg(4, f(a,b,c,d), Arg).", [["Arg = d"]]);

    assert_prolog_success!(&mut wam, "?- catch(arg(N, f, Arg), type_error(E), true).",
                           [["E = compound_expected", "Arg = _3", "N = _1"]]);
    assert_prolog_success!(&mut wam, "?- catch(arg(N, _, Arg), E, true).",
                           [["E = instantiation_error", "Arg = _3", "N = _1"]]);

    assert_prolog_success!(&mut wam, "?- arg(N, f(X, Y, Z), arg_val).",
                           [["X = arg_val", "Y = _3", "N = 1", "Z = _4"],
                            ["X = _2", "Y = arg_val", "N = 2", "Z = _4"],
                            ["X = _2", "Y = _3", "N = 3", "Z = arg_val"]]);

    assert_prolog_success!(&mut wam, "?- arg(N, f(arg, not_arg, arg, X), arg).",
                           [["X = _5", "N = 1"],
                            ["X = _5", "N = 3"],
                            ["X = arg", "N = 4"]]);

    assert_prolog_failure!(&mut wam, "?- arg(N, f(arg, arg, arg), not_arg).");
    assert_prolog_failure!(&mut wam, "?- arg(1, f(arg, not_arg, not_arg), not_arg).");
    assert_prolog_success!(&mut wam, "?- arg(2, f(arg, not_arg, not_arg), not_arg).");
    assert_prolog_success!(&mut wam, "?- arg(3, f(arg, not_arg, not_arg), not_arg).");

    assert_prolog_success!(&mut wam, "?- functor(f(a,b,c), F, Arity).",
                           [["F = f", "Arity = 3"]]);

    assert_prolog_success!(&mut wam, "?- functor(f(a,b,c), F, N).",
                           [["F = f", "N = 3"]]);
    assert_prolog_failure!(&mut wam, "?- functor(f(a,b,c), g, N).");
    assert_prolog_success!(&mut wam, "?- functor(f(a,b,c), F, 3).", [["F = f"]]);
    assert_prolog_failure!(&mut wam, "?- functor(f(a,b,c), F, 4).");
    assert_prolog_failure!(&mut wam, "?- functor(f(a,b,c), g, 3).");

    assert_prolog_success!(&mut wam, "?- functor(F, f, 0).", [["F = f"]]);

    assert_prolog_success!(&mut wam, "?- functor(Func, f, 3).", [["Func = f(_2, _3, _4)"]]);
    assert_prolog_success!(&mut wam, "?- functor(Func, f, 4).", [["Func = f(_2, _3, _4, _5)"]]);

    assert_prolog_success!(&mut wam, "?- catch(functor(F, \"sdf\", 3), E, true).",
                           [["E = instantiation_error", "F = _1"]]);
    assert_prolog_success!(&mut wam, "?- catch(functor(Func, F, 3), E, true).",
                           [["E = instantiation_error", "Func = _1", "F = _2"]]);
    assert_prolog_success!(&mut wam, "?- catch(functor(Func, f, N), E, true).",
                           [["E = instantiation_error", "Func = _1", "N = _3"]]);
    assert_prolog_failure!(&mut wam, "?- catch(functor(Func, f, N), E, false).");

    assert_prolog_success!(&mut wam, "?- X is 3, call(integer, X).");
    assert_prolog_failure!(&mut wam, "?- X is 3 + 3.5, call(integer, X).");
    assert_prolog_success!(&mut wam, "?- X is 3 + 3.5, \\+ call(integer, X).");
    assert_prolog_success!(&mut wam, "?- X is 3 + 3.5, \\+ integer(X).");

    assert_prolog_success!(&mut wam, "?- Func =.. [atom].", [["Func = atom"]]);
    assert_prolog_success!(&mut wam, "?- Func =.. [\"sdf\"].", [["Func = \"sdf\""]]);
    assert_prolog_success!(&mut wam, "?- Func =.. [1].", [["Func = 1"]]);
    assert_prolog_success!(&mut wam, "?- catch(Func =.. [1,2], instantiation_error, true).");
    assert_prolog_success!(&mut wam, "?- f(1,2,3) =.. List.", [["List = [f, 1, 2, 3]"]]);
    assert_prolog_success!(&mut wam, "?- f(1,2,3) =.. [f,1,2,3].");
    assert_prolog_failure!(&mut wam, "?- f(1,2,3) =.. [f,1].");
    assert_prolog_failure!(&mut wam, "?- f(1,2,3) =.. [g,1,2,3].");
    assert_prolog_success!(&mut wam, "?- f(1,2,3) =.. [f,X,Y,Z].",
                           [["X = 1", "Y = 2", "Z = 3"]]);

    assert_prolog_success_with_limit!(&mut wam, "?- length(Xs, N).",
                                      [["N = 0", "Xs = []"],
                                       ["N = 1", "Xs = [_3]"],
                                       ["N = 2", "Xs = [_3, _6]"],
                                       ["N = 3", "Xs = [_3, _6, _9]"],
                                       ["N = 4", "Xs = [_3, _6, _9, _12]"],
                                       ["N = 5", "Xs = [_3, _6, _9, _12, _15]"]],
                                      6);

    assert_prolog_success!(&mut wam, "?- length(Xs, 3).", [["Xs = [_2, _5, _8]"]]);
    assert_prolog_success!(&mut wam, "?- length([a,b,c], N).", [["N = 3"]]);
    assert_prolog_success!(&mut wam, "?- length([], N).", [["N = 0"]]);
    assert_prolog_success!(&mut wam, "?- length(Xs, 0).", [["Xs = []"]]);
    assert_prolog_success!(&mut wam, "?- length([a,b,[a,b,c]], 3).");
    assert_prolog_failure!(&mut wam, "?- length([a,b,[a,b,c]], 2).");
    assert_prolog_success!(&mut wam, "?- catch(length(a, []), type_error(_, E), true).",
                           [["E = []"]]);

    assert_prolog_success!(&mut wam, "?- duplicate_term([1,2,3], [X,Y,Z]).",
                           [["Z = 3", "Y = 2", "X = 1"]]);
    assert_prolog_success!(&mut wam, "?- duplicate_term(f(X, [a], Z), f(X, Y, Z)).",
                           [["X = _3", "Y = [a]", "Z = _5"]]);
    assert_prolog_failure!(&mut wam, "?- duplicate_term(g(X), f(X)).");
    assert_prolog_success!(&mut wam, "?- duplicate_term(f(X), f(X)).",
                           [["X = _1"]]);

    assert_prolog_success!(&mut wam, "?- float(3.14159269).");
    assert_prolog_failure!(&mut wam, "?- float(3).");
    assert_prolog_failure!(&mut wam, "?- float(\"sdfsa\").");
    assert_prolog_failure!(&mut wam, "?- float(atom).");
    assert_prolog_failure!(&mut wam, "?- float(structure(functor)).");
    assert_prolog_failure!(&mut wam, "?- float([1,2,3]).");
    assert_prolog_failure!(&mut wam, "?- float([1,2,X]).");
    assert_prolog_failure!(&mut wam, "?- X is 3 rdiv 4, float(X).");

    assert_prolog_success!(&mut wam, "?- X is 3 rdiv 4, rational(X).");
    assert_prolog_failure!(&mut wam, "?- rational(3).");
    assert_prolog_failure!(&mut wam, "?- rational(f(X)).");
    assert_prolog_failure!(&mut wam, "?- rational(\"sdfsa\").");
    assert_prolog_failure!(&mut wam, "?- rational(atom).");
    assert_prolog_failure!(&mut wam, "?- rational(structure(functor)).");
    assert_prolog_failure!(&mut wam, "?- rational([1,2,3]).");
    assert_prolog_failure!(&mut wam, "?- rational([1,2,X]).");

    assert_prolog_success!(&mut wam, "?- compound(functor(compound)).");
    assert_prolog_success!(&mut wam, "?- compound(f(X)).");
    assert_prolog_success!(&mut wam, "?- compound([1,2,3]).");
    assert_prolog_failure!(&mut wam, "?- compound([]).");
    assert_prolog_failure!(&mut wam, "?- compound(3.14159269).");
    assert_prolog_failure!(&mut wam, "?- compound(3).");
    assert_prolog_failure!(&mut wam, "?- compound(\"sdfsa\").");
    assert_prolog_failure!(&mut wam, "?- compound(atom).");

    assert_prolog_failure!(&mut wam, "?- string(functor(string)).");
    assert_prolog_failure!(&mut wam, "?- string(3.14159269).");
    assert_prolog_failure!(&mut wam, "?- string(3).");
    assert_prolog_failure!(&mut wam, "?- string(f(X)).");
    assert_prolog_success!(&mut wam, "?- string(\"sdfsa\").");
    assert_prolog_failure!(&mut wam, "?- string(atom).");
    assert_prolog_failure!(&mut wam, "?- string([1,2,3]).");
    assert_prolog_failure!(&mut wam, "?- string([1,2,X]).");

    assert_prolog_success!(&mut wam, "?- X = nonvar, nonvar(X).");
    assert_prolog_failure!(&mut wam, "?- nonvar(X).");
    assert_prolog_success!(&mut wam, "?- nonvar(f(X)).");
    assert_prolog_success!(&mut wam, "?- nonvar(functor(nonvar)).");
    assert_prolog_success!(&mut wam, "?- nonvar(3.14159269).");
    assert_prolog_success!(&mut wam, "?- nonvar(3).");
    assert_prolog_success!(&mut wam, "?- nonvar(\"sdfsa\").");
    assert_prolog_success!(&mut wam, "?- nonvar(atom).");
    assert_prolog_success!(&mut wam, "?- nonvar([1,2,3]).");
    assert_prolog_success!(&mut wam, "?- nonvar([1,2,X]).");

    assert_prolog_success!(&mut wam, "?- A = f(A), ground(f(f(A))), ground(f(A)), ground(A).");
    assert_prolog_failure!(&mut wam, "?- B = f(A), ground(B).");
    assert_prolog_failure!(&mut wam, "?- B = f(A), ground(A).");

    assert_prolog_success!(&mut wam, "?- ground(x), ground(f(x)), X = f(x), ground(g(f(X), [a,b])).");

    assert_prolog_success!(&mut wam, "?- A = f(A), g(A, B) == g(f(A), B).");
    assert_prolog_failure!(&mut wam, "?- A = f(A), g(A, B) == g(f(A), b).");
    assert_prolog_failure!(&mut wam, "?- A == B.");
    assert_prolog_failure!(&mut wam, "?- A == 12.1.");
    assert_prolog_success!(&mut wam, "?- X = x, f(X, x) == f(x, X).");

    assert_prolog_failure!(&mut wam, "?- A = f(A), g(A, B) \\== g(f(A), B).");
    assert_prolog_success!(&mut wam, "?- A = f(A), g(A, B) \\== g(f(A), b).");
    assert_prolog_success!(&mut wam, "?- A \\== B.");
    assert_prolog_success!(&mut wam, "?- A \\== 12.1.");
    assert_prolog_failure!(&mut wam, "?- X = x, f(X, x) \\== f(x, X).");

    assert_prolog_success!(&mut wam, "?- X @=< Y.");
    assert_prolog_failure!(&mut wam, "?- X @>= Y.");
    assert_prolog_failure!(&mut wam, "?- X @> Y.");
    assert_prolog_success!(&mut wam, "?- X @>= X.");
    assert_prolog_failure!(&mut wam, "?- atom @=< \"string\".");
    assert_prolog_success!(&mut wam, "?- atom @=< atom.");
    assert_prolog_failure!(&mut wam, "?- atom @=< aaa.");
    assert_prolog_success!(&mut wam, "?- atom @>= \"string\".");
    assert_prolog_success!(&mut wam, "?- X is 3 + 3, X @>= Y.");
    assert_prolog_success!(&mut wam, "?- f(X) @>= f(X).");
    assert_prolog_success!(&mut wam, "?- f(X) @>= a.");
    assert_prolog_failure!(&mut wam, "?- f(X) @=< a.");
    assert_prolog_success!(&mut wam, "?- [1,2] @=< [1,2].");
    assert_prolog_failure!(&mut wam, "?- [1,2,3] @=< [1,2].");
    assert_prolog_success!(&mut wam, "?- [] @=< [1,2].");
    assert_prolog_failure!(&mut wam, "?- [] @< 1.");
    assert_prolog_failure!(&mut wam, "?- [] @< \"string\".");
    assert_prolog_failure!(&mut wam, "?- [] @< atom.");
    assert_prolog_success!(&mut wam, "?- atom @< [].");
    assert_prolog_failure!(&mut wam, "?- 1.1 @< 1.");
    assert_prolog_success!(&mut wam, "?- 1.0 @=< 1.");
    assert_prolog_success!(&mut wam, "?- 1 @=< 1.0."); //TODO: currently this succeeds. make it fail.

    assert_prolog_success!(&mut wam, "?- X =@= Y.");
    assert_prolog_failure!(&mut wam, "?- f(X) =@= f(x).");
    assert_prolog_failure!(&mut wam, "?- X \\=@= X.");
    assert_prolog_success!(&mut wam, "?- f(x) =@= f(x).");
    assert_prolog_failure!(&mut wam, "?- [X,Y,Z] =@= [V,W,V].");
    assert_prolog_success!(&mut wam, "?- [X,Y,Z] =@= [V,W,Z].");
    assert_prolog_success!(&mut wam, "?- [X,Y,X] =@= [V,W,V].");
    assert_prolog_success!(&mut wam, "?- g(B) = B, g(A) = A, A =@= B.");

    assert_prolog_success!(&mut wam, "?- call(((G = 2 ; fail), B=3, !)).",
                           [["G = 2", "B = 3"]]);

    assert_prolog_success!(&mut wam, "?- call_with_inference_limit((setup_call_cleanup(S=1,(G=2;fail),display(S+G>B)), B=3, !), 100, R).",
                           [["G = 2", "B = 3", "R = !", "S = 1"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit((setup_call_cleanup(S=1,(G=2;fail),display(S+G>B)), B=3, !), 10, R).",
                           [["S = _1", "G = _4", "B = _14", "R = inference_limit_exceeded"]]);
}

#[test]
fn test_queries_on_setup_call_cleanup()
{
    let mut wam = Machine::new();

    // Test examples from the ISO Prolog page for setup_call_catch.
    assert_prolog_failure!(&mut wam, "?- setup_call_cleanup(false, _, _).");
    assert_prolog_success!(&mut wam, "?- catch(setup_call_cleanup(true, throw(unthrown), _), instantiation_error, true).");
    assert_prolog_success!(&mut wam, "?- setup_call_cleanup(true, true, (true ; throw(x))).");
    assert_prolog_success!(&mut wam, "?- setup_call_cleanup(true, X = 1, X = 2).",
                           [["X = 1"]]);
    assert_prolog_success!(&mut wam, "?- setup_call_cleanup(true, true, X = 2).",
                           [["X = 2"]]);
    assert_prolog_success!(&mut wam, "?- catch(setup_call_cleanup(true, X=true, X), E, true).",
                           [["E = instantiation_error", "X = _1"]]);
    assert_prolog_success!(&mut wam, "?- catch(setup_call_cleanup(X=throw(ex), true, X), E, true).",
                           [["E = ex", "X = _3"]]);
    assert_prolog_success!(&mut wam, "?- setup_call_cleanup(true, true, false).");
    assert_prolog_success!(&mut wam, "?- setup_call_cleanup(S = 1, G = 2, C = 3).",
                           [["S = 1", "G = 2", "C = 3"]]);
    assert_prolog_success!(&mut wam, "?- setup_call_cleanup((S=1;S=2), G=3, C=4).",
                           [["S = 1", "G = 3", "C = 4"]]);
    assert_prolog_success!(&mut wam, "?- setup_call_cleanup(S=1, G=2, display(S+G)).",
                           [["S = 1", "G = 2"]]);
    assert_prolog_success!(&mut wam, "?- setup_call_cleanup(S=1, (G=2;G=3), display(S+G)).",
                           [["S = 1", "G = 2"],
                            ["S = 1", "G = 3"]]);
    assert_prolog_success!(&mut wam, "?- setup_call_cleanup(S=1, G=2, display(S+G>A+B)), A=3, B=4.",
                           [["S = 1", "G = 2", "A = 3", "B = 4"]]);
    assert_prolog_success!(&mut wam,
                           "?- catch(setup_call_cleanup(S=1, (G=2;G=3,throw(x)), display(S+G)), E, true).",
                           [["S = 1", "G = 2", "E = _26"], ["G = _4", "E = x", "S = _1"]]);
    assert_prolog_success!(&mut wam,
                           "?- setup_call_cleanup(S=1, (G=2;G=3),display(S+G>B)), B=4, !.",
                           [["S = 1", "B = 4", "G = 2"]]);
    assert_prolog_success!(&mut wam,
                           "?- setup_call_cleanup(S=1,G=2,display(S+G>B)),B=3,!.",
                           [["S = 1", "G = 2", "B = 3"]]);
    assert_prolog_success!(&mut wam,
                           "?- setup_call_cleanup(S=1,(G=2;false),display(S+G>B)),B=3,!.",
                           [["S = 1", "G = 2", "B = 3"]]);
    assert_prolog_success!(&mut wam,
                           "?- setup_call_cleanup(S=1,(G=2;S=2),display(S+G>B)), B=3, !.",
                           [["S = 1", "B = 3", "G = 2"]]);
    assert_prolog_failure!(&mut wam,
                           "?- setup_call_cleanup(S=1,(G=2;G=3), display(S+G>B)), B=4, !, throw(x).");
    assert_prolog_success!(&mut wam,
                           "?- setup_call_cleanup(true, (X=1;X=2), display(a)), setup_call_cleanup(true,(Y=1;Y=2),display(b)), !.",
                           [["Y = 1", "X = 1"]]);
    assert_prolog_success!(&mut wam, "?- catch(setup_call_cleanup(true,throw(goal),throw(cl)), Pat, true).",
                           [["Pat = goal"]]);
    assert_prolog_success!(&mut wam, "?- catch(( setup_call_cleanup(true,(G=1;G=2),throw(cl)), throw(cont)), Pat, true).",
                           [["Pat = cont", "G = _1"]]);
}

#[test]
fn test_queries_on_call_with_inference_limit()
{
    let mut wam = Machine::new();

    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(throw(error), 0, R).",
                           [["R = inference_limit_exceeded"]]);
    assert_prolog_success!(&mut wam, "?- catch(call_with_inference_limit(throw(error), 1, R), error, true).");

    assert_prolog_failure!(&mut wam, "?- call_with_inference_limit(g(X), 5, R).");

    submit(&mut wam, "g(1). g(2). g(3). g(4). g(5).");

    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(g(X), 5, R).",
                           [["R = true", "X = 1"],
                            ["R = true", "X = 2"],
                            ["R = true", "X = 3"],
                            ["R = true", "X = 4"],
                            ["R = !", "X = 5"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(g(X), 5, R), call(true).",
                           [["R = true", "X = 1"],
                            ["R = true", "X = 2"],
                            ["R = true", "X = 3"],
                            ["R = true", "X = 4"],
                            ["R = !", "X = 5"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(g(X), 2, R).",
                           [["R = true", "X = 1"],
                            ["R = true", "X = 2"],
                            ["R = inference_limit_exceeded", "X = _1"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(g(X), 3, R1),
                                         call_with_inference_limit(g(X), 5, R2).",
                           [["X = 1", "R1 = true", "R2 = !"],
                            ["X = 2", "R1 = true", "R2 = !"],
                            ["X = 3", "R1 = true", "R2 = !"],
                            ["X = 4", "R1 = true", "R2 = !"],
                            ["X = 5", "R1 = !", "R2 = !"]]);

    submit(&mut wam, "f(X) :- call_with_inference_limit(g(X), 5, _).");

    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(f(X), 6, R).",
                           [["R = true", "X = 1"],
                            ["R = true", "X = 2"],
                            ["R = true", "X = 3"],
                            ["R = true", "X = 4"],
                            ["R = !", "X = 5"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(f(X), 5, R).",
                           [["R = true", "X = 1"],
                            ["R = true", "X = 2"],
                            ["R = true", "X = 3"],
                            ["R = true", "X = 4"],
                            ["R = inference_limit_exceeded", "X = _1"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(f(X), 3, R).",
                           [["R = true", "X = 1"],
                            ["R = true", "X = 2"],
                            ["R = inference_limit_exceeded", "X = _1"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(f(X), 2, R).",
                           [["R = true", "X = 1"],
                            ["R = inference_limit_exceeded", "X = _1"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(f(X), 1, R).",
                           [["R = inference_limit_exceeded", "X = _1"]]);

    submit(&mut wam, "e(X) :- call_with_inference_limit(f(X), 10, _).");

    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(e(X), 7, R).",
                           [["R = true", "X = 1"],
                            ["R = true", "X = 2"],
                            ["R = true", "X = 3"],
                            ["R = true", "X = 4"],
                            ["R = !", "X = 5"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(e(X), 6, R).",
                           [["R = true", "X = 1"],
                            ["R = true", "X = 2"],
                            ["R = true", "X = 3"],
                            ["R = true", "X = 4"],
                            ["R = inference_limit_exceeded", "X = _1"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(e(X), 4, R).",
                           [["R = true", "X = 1"],
                            ["R = true", "X = 2"],
                            ["R = inference_limit_exceeded", "X = _1"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(e(X), 3, R).",
                           [["R = true", "X = 1"],
                            ["R = inference_limit_exceeded", "X = _1"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(e(X), 2, R).",
                           [["R = inference_limit_exceeded", "X = _1"]]);

    submit(&mut wam, "f(X, R) :- call_with_inference_limit(g(X), 5, R).");

    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(f(X, R), 3, S).",
                           [["S = true", "X = 1", "R = true"],
                            ["S = true", "X = 2", "R = true"],
                            ["S = inference_limit_exceeded", "X = _1", "R = _2"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(f(X, R), 7, R).",
                           [["R = true", "X = 1"],
                            ["R = true", "X = 2"],
                            ["R = true", "X = 3"],
                            ["R = true", "X = 4"],
                            ["R = !", "X = 5"]]);

    submit(&mut wam, "g(1). g(2). g(3). g(4). g(5). g(6).");

    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(f(X, R), 7, S).",
                           [["R = true", "X = 1", "S = true"],
                            ["R = true", "X = 2", "S = true"],
                            ["R = true", "X = 3", "S = true"],
                            ["R = true", "X = 4", "S = true"],
                            ["R = true", "X = 5", "S = true"],
                            ["R = inference_limit_exceeded", "S = !", "X = _1"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(g(X), 2, R), call_with_inference_limit(g(X), 1, S).",
                           [["R = true", "X = 1", "S = !"],
                            ["R = true", "X = 2", "S = !"],
                            ["R = true", "X = 3", "S = !"],
                            ["R = true", "X = 4", "S = !"],
                            ["R = true", "X = 5", "S = !"],
                            ["R = !", "X = 6", "S = !"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(g(X), 2, R), call_with_inference_limit(g(X), 1, R).",
                           [["R = !", "X = 6"]]);
    assert_prolog_success!(&mut wam, "?- call_with_inference_limit(g(X), 1, R), call_with_inference_limit(g(X), 1, R).",
                           [["R = inference_limit_exceeded", "X = _1"]]);
    
}
