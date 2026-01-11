

module Preorder {
    datatype Tree = Node(val: int, left: Tree, right: Tree) | Nil
    function PreorderTraversal(root: Tree): seq<Tree>
        // ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil
        // ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil && (x == root || x in TreePreorderTraversal(root.left) || x in TreePreorderTraversal(root.right))
        // ensures forall x :: x in root.repr ==> x in PreorderTraversal(root)
        // ensures injectiveSeq(TreePreorderTraversal(root))
        // ensures forall k :: 0 <= k < |TreePreorderTraversal(root)| ==> TreePreorderTraversal(root)[k] in root.repr
        // ensures forall k :: 0 <= k < |PreorderTraversal(root)| ==> forall child :: child in PreorderTraversal(root)[k].repr && child != child in PreorderTraversal(root)[k] ==> exists j :: k < j < |PreorderTraversal(root)| && PreorderTraversal(root)[j] == child
    {
        if root == Nil then
            []
        else if root.left != Nil && root.right != Nil then
            [root]+PreorderTraversal(root.left)+PreorderTraversal(root.right)
        else if root.left != Nil then
            [root]+PreorderTraversal(root.left)
        else if root.right != Nil then
            [root]+PreorderTraversal(root.right)
        else
            [root]
    }

    lemma PreorderTraveralSize(tree: Tree) 
        requires ValidNode(tree)
        ensures |PreorderTraversal(tree)| == |nodeSet(tree)|
    {}

    function SeqPreorderTraversal(trees: seq<Tree>): seq<Tree> {
        if trees == [] then
            []
        else PreorderTraversal(trees[0]) + SeqPreorderTraversal(trees[1..])
    }

    function childStack(node: Tree): seq<Tree> {
        if node == Nil then []
        else if node.right.Node? && node.left.Node? then
            [node.right, node.left]
        else if node.right.Node? then
            [node.right]
        else if node.left.Node? then
            [node.left]
        else
            []
    }

    function nodeSet(root: Tree): set<Tree> {
        if root.Nil?  then {}
        else
            {root} + nodeSet(root.left)+nodeSet(root.right)
    }

    function nodes(tress: seq<Tree>): set<Tree> {
        if tress == [] then {}
        else {tress[0]} + nodes(tress[1..])
    }

    function UnionNodes(roots: seq<Tree>): set<Tree> 
        ensures forall r :: r in roots && r.Node? ==> r in UnionNodes(roots)
    {
        if roots == [] then {}
        else nodeSet(roots[0])+UnionNodes(roots[1..])
    }

    function StackToPreorder(s: seq<Tree>): seq<Tree> {
    if s == [] then []
    else 
        // Process the top of the stack (the last element), then the rest
        PreorderTraversal(s[|s|-1]) + StackToPreorder(s[..|s|-1])
    }

    lemma Lemma_StackToPreorder_App(a: seq<Tree>, b: seq<Tree>)
    ensures StackToPreorder(a + b) == StackToPreorder(b) + StackToPreorder(a)
{
    if b == [] {
        assert a + b == a;
    } else {
        // b has elements. (a+b) ends with b's last element.
        // StackToPreorder(a+b) 
        // == Preorder((a+b).last) + StackToPreorder((a+b).dropLast)
        // == Preorder(b.last) + StackToPreorder(a + b.dropLast)
        // Recurse...
        assert a+b == a+b[..|b|-1] + [b[|b|-1]];
        Lemma_StackToPreorder_App(a, b[..|b|-1]);
    }
}

lemma Lemma_PreserveInvariant(prefix: seq<Tree>, current: Tree)
        requires current != Nil
        ensures [current] + StackToPreorder(prefix + childStack(current)) == StackToPreorder(prefix + [current])
    {
        var children := childStack(current);

        // Step 1: Expand the LHS (New Stack)
        // StackToPreorder(prefix + children) -> StackToPreorder(children) + StackToPreorder(prefix)
        Lemma_StackToPreorder_App(prefix, children);

        // Step 2: Expand the RHS (Old Stack)
        // StackToPreorder(prefix + [current]) -> StackToPreorder([current]) + StackToPreorder(prefix)
        Lemma_StackToPreorder_App(prefix, [current]);

        // Step 3: Show that [current] + ChildrenWork == CurrentWork
        // StackToPreorder(children) is effectively Preorder(left) + Preorder(right)
        // Preorder(current) is [current] + Preorder(left) + Preorder(right)
        
        // Dafny can auto-verify the definitions here, but we state the equivalence clearly:
        assert [current] + StackToPreorder(children) == PreorderTraversal(current);
    }

    lemma {:verify false} Lemma_StackTopIsPreorderHead(prefix: seq<Tree>, current: Tree)
        requires current.Node? // or current != Nil
        requires forall n :: n in prefix ==> n != Nil
        ensures 
            var new_stack := prefix + childStack(current);
            |new_stack| > 0 ==> 
            new_stack[|new_stack|-1] == StackToPreorder(new_stack)[0]
    {
        var children := childStack(current);
        var new_stack := prefix + children;

        // 1. Establish that all nodes in the new stack are valid (not Nil)
        // This is required to ensure PreorderTraversal(node) is not empty.
        forall c | c in children 
            ensures c != Nil 
        {
            // childStack logic only includes nodes if they match .Node? or != Nil
        }
        assert forall n :: n in new_stack ==> n != Nil;

        if |new_stack| > 0 {
            // 2. Identify the top of the stack
            var top := new_stack[|new_stack|-1];
            
            // 3. Expand the definition of StackToPreorder for the new stack
            // StackToPreorder(s) == PreorderTraversal(s.last) + ...
            assert StackToPreorder(new_stack) == PreorderTraversal(top) + StackToPreorder(new_stack[..|new_stack|-1]);
            
            // 4. Expand PreorderTraversal for the top node
            // Since top != Nil, it generates a sequence starting with itself
            assert PreorderTraversal(top) == [top] + PreorderTraversal(top.left) + PreorderTraversal(top.right);
            
            // 5. Conclusion
            // StackToPreorder(new_stack) starts with [top] + ...
            // Therefore, its first element is 'top'.
            assert StackToPreorder(new_stack)[0] == top;
        }
    }

    lemma Lemma_UnionNodes_App(a: seq<Tree>, b: seq<Tree>)
        ensures UnionNodes(a + b) == UnionNodes(a) + UnionNodes(b)
    {
        if a == [] {
            assert a + b == b;
        } else {
            assert (a+b)[1..] == a[1..]+b;
            Lemma_UnionNodes_App(a[1..], b);
        }
    }

    lemma TreeUnionLemma(nodes: seq<Tree>)
        ensures forall x :: x in UnionNodes(nodes) ==> exists k :: 0 <= k < |nodes| && x in nodeSet(nodes[k])
    {

    }

    lemma TreeUnionMaint(stack: seq<Tree>, current: Tree, unvisited: set<Tree>)
        requires |stack| > 0
        requires current.Node?
        requires unvisited == UnionNodes(stack)
        requires AllDisjoint(stack)
        requires forall x :: x in stack ==> ValidNode(x)
        requires current == stack[|stack|-1]
        ensures UnionNodes(stack[..|stack|-1]+childStack(current)) == unvisited-{current}
    {
        // childStackLemma(current);
        assert current in stack;
        // assert current.Valid();
        assert stack == stack[..|stack|-1]+[stack[|stack|-1]];
        Lemma_UnionNodes_App(stack[..|stack|-1],[stack[|stack|-1]]);
        // assert TreeUnion(stack) == TreeUnion(stack[..|stack|-1])+TreeUnion([stack[|stack|-1]]);
        assert UnionNodes([stack[|stack|-1]]) == nodeSet(current);
        assert UnionNodes(stack[..|stack|-1]) !! nodeSet(current) by {
            forall x | x in UnionNodes(stack[..|stack|-1])
                ensures x !in nodeSet(current)
            {
                TreeUnionLemma(stack[..|stack|-1]);
                var xx :| xx in stack[..|stack|-1] && x in nodeSet(xx);
                // var k :| 0 <= k < |stack[..|stack|-1]| && x in stack[..|stack|-1][k].repr;
                // assert stack[..|stack|-1][k].repr !! current.repr;
            }
        }
        // assert TreeUnion(stack[..|stack|-1]) == unvisited-current.repr;
        if current.left != Nil && current.right != Nil {
            assert nodeSet(current.right) + nodeSet(current.left) + {current} == nodeSet(current);
            assert nodeSet(current.right) + nodeSet(current.left) == nodeSet(current) - {current};
            Lemma_UnionNodes_App([current.right],[current.left]);
            // assert TreeUnion([current.right, current.left]) == current.right.repr + current.left.repr;
            Lemma_UnionNodes_App(stack[..|stack|-1], [current.right, current.left]);
        } else if current.left != Nil && current.right == Nil {
            assert nodeSet(current.left) == nodeSet(current) - {current};
            Lemma_UnionNodes_App(stack[..|stack|-1], [current.left]);
            
        }else if current.left == Nil && current.right != Nil {
            assert nodeSet(current.right) == nodeSet(current) - {current};
            // assert current.right.repr == current.repr - {current};
            Lemma_UnionNodes_App(stack[..|stack|-1], [current.right]);

        }else if current.left == Nil && current.right == Nil {
            Lemma_UnionNodes_App(stack[..|stack|-1], []);

        }
    }

    predicate ValidNode(tree: Tree) {
        if tree.Nil? then true
        else 
            tree !in nodeSet(tree.left) 
            && tree !in nodeSet(tree.right)
            && nodeSet(tree.left) !! nodeSet(tree.right)
            && ValidNode(tree.left)
            && ValidNode(tree.right)
    }

    ghost predicate AllDisjoint(ts: seq<Tree>)
    {
        forall x, y :: 0 <= x < y < |ts| && x != y ==> nodeSet(ts[x]) !! nodeSet(ts[y])
    }

    lemma  AllDisjointMaint(stack: seq<Tree>, current: Tree)
        requires ValidNode(current)
        requires |stack| > 0
        requires AllDisjoint(stack)
        requires forall node :: node in stack ==> node.Node?
        requires current == stack[|stack|-1]
        ensures current.left != Nil && current.right != Nil ==> AllDisjoint(stack[..|stack|-1]+[current.right, current.left])
        ensures current.left != Nil && current.right == Nil ==> AllDisjoint(stack[..|stack|-1]+[current.left])
        ensures current.left == Nil && current.right != Nil ==> AllDisjoint(stack[..|stack|-1]+[current.right])
        ensures current.left == Nil && current.right == Nil ==> AllDisjoint(stack[..|stack|-1])
    {
            if current.right != Nil && current.left != Nil {
                assert nodeSet(current.right) !! nodeSet(current.left);
                assert AllDisjoint(stack[..|stack|-1]+[current.right, current.left]);
            } else if current.right != Nil && current.left == Nil {
                // assert current.right.repr < current.repr;
                // assert AllDisjoint(stack[..|stack|-1]+[current.right]);
            } else if current.right == Nil && current.left != Nil {
                // assert AllDisjoint(stack[..|stack|-1]+[current.left]);
            }else {
                // assert AllDisjoint(stack[..|stack|-1]);
            }
    }

    method TraverseBasic(root: Tree) returns (result: seq<Tree>)
        requires !root.Nil?
        requires ValidNode(root)
        ensures result == PreorderTraversal(root)
    {
        result := [];
        ghost var visited: set<Tree> := {};
        ghost var unvisited: set<Tree> := nodeSet(root);
        // ghost var totalSize := |PreorderTraversal(root)|;
        PreorderTraveralSize(root);
        var stack := [root];
        var i := 0;
        while |stack| > 0
            invariant forall s :: s in stack ==> !s.Nil? && ValidNode(s)
            invariant forall n :: n in result ==> n in visited
            invariant forall n :: n in visited ==> n in result
            invariant visited !! unvisited
            // invariant visited + unvisited == nodeSet(root)
            invariant AllDisjoint(stack)
            invariant |result| == |visited| == i
            invariant 0 <= i <= |PreorderTraversal(root)|
            invariant UnionNodes(stack) == unvisited
            invariant visited + UnionNodes(stack) == nodeSet(root)
            invariant result + StackToPreorder(stack) == PreorderTraversal(root)
            // invariant StackToPreorder(stack) == PreorderTraversal(root)[i..]
            // invariant |stack| > 0 ==> stack[|stack|-1] == StackToPreorder(stack)[0]
            // invariant |stack| > 0 ==> stack[|stack|-1] == PreorderTraversal(root)[i]
            // invariant result == PreorderTraversal(root)[..i]
            // decreases nodeSet(root) - visited
            // decreases totalSize - |result|
            decreases |unvisited|
        {
            var current := stack[|stack|-1];
            var children := childStack(current);
            var old_stack := stack;
            TreeUnionMaint(stack, current, unvisited);
            AllDisjointMaint(stack, current);
            assert stack == stack[..|stack|-1] + [stack[|stack|-1]];
            // assert current in UnionNodes([stack[|stack|-1]]);
            Lemma_UnionNodes_App(stack[..|stack|-1], [stack[|stack|-1]]);
            Lemma_StackToPreorder_App(stack[..|stack|-1], children);
            Lemma_PreserveInvariant(stack[..|stack|-1], current);
            assert result+[current]+StackToPreorder(stack[..|stack|-1] + childStack(current)) == PreorderTraversal(root);
            // TreeUnionLemma(stack);
            // assert current == stack[|stack|-1];
            // assert current in stack;
            // assert current in unvisited;
            stack := stack[..|stack|-1]+childStack(current);
            // assert PreorderTraversal(root)[..i+1] == PreorderTraversal(root)[..i]+[PreorderTraversal(root)[i]];
            // assert PreorderTraversal(root)[i..] == [PreorderTraversal(root)[i]]+PreorderTraversal(root)[i+1..];
            // assert current !in visited;
            result := result + [current];
            visited := visited+{current};
            unvisited := unvisited - {current};
            i := i + 1;
            // assert unvisited == {} ==> |stack| == 0;
        
        // StackToPreorder(children) needs to equal Preorder(current.left) + Preorder(current.right)
        // children is roughly [right, left]. 
        // StackToPreorder([right, left]) = Preorder(left) + Preorder(right)
        // This matches PreorderTraversal(current) body!
        // assert StackToPreorder(children) == PreorderTraversal(current.left) + PreorderTraversal(current.right);

        // 2. Prove the Set Invariant
        // We need: nodes(result') + UnionNodes(stack') == nodeSet(root)
            Lemma_UnionNodes_App(old_stack[..|old_stack|-1], children);
        }
        // assert |visited| == totalSize;
        // assert result == PreorderTraversal(root);
        return result;
    }

    method TraverseBasicClean(root: Tree) returns (result: seq<Tree>)
        requires !root.Nil?
        requires ValidNode(root)
        ensures result == PreorderTraversal(root)
    {
        result := [];
        ghost var visited: set<Tree> := {};
        ghost var unvisited: set<Tree> := nodeSet(root);
        PreorderTraveralSize(root);
        var stack := [root];
        var i := 0;
        while |stack| > 0
            invariant forall s :: s in stack ==> !s.Nil? && ValidNode(s)
            invariant forall n :: n in result ==> n in visited
            invariant forall n :: n in visited ==> n in result
            invariant visited !! unvisited
            invariant AllDisjoint(stack)
            invariant |result| == |visited| == i
            invariant 0 <= i <= |PreorderTraversal(root)|
            invariant UnionNodes(stack) == unvisited
            invariant visited + UnionNodes(stack) == nodeSet(root)
            invariant result + StackToPreorder(stack) == PreorderTraversal(root)
            decreases |unvisited|
        {
            var current := stack[|stack|-1];
            var children := childStack(current);
            var old_stack := stack;
            TreeUnionMaint(stack, current, unvisited);
            AllDisjointMaint(stack, current);
            assert stack == stack[..|stack|-1] + [stack[|stack|-1]];
            Lemma_UnionNodes_App(stack[..|stack|-1], [stack[|stack|-1]]);
            Lemma_StackToPreorder_App(stack[..|stack|-1], children);
            Lemma_PreserveInvariant(stack[..|stack|-1], current);
            assert result+[current]+StackToPreorder(stack[..|stack|-1] + childStack(current)) == PreorderTraversal(root);
            stack := stack[..|stack|-1]+childStack(current);
            result := result + [current];
            visited := visited+{current};
            unvisited := unvisited - {current};
            i := i + 1;
            Lemma_UnionNodes_App(old_stack[..|old_stack|-1], children);
        }
        return result;
    }
}