package kodkod.examples.propagating;

import kodkod.ast.ConstantExpression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.propagating.DownwardExpressionBoundPropagator;
import kodkod.engine.propagating.ExpressionBounds;
import kodkod.engine.propagating.UpwardExpressionBoundPropagator;
import kodkod.instance.Bounds;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

public class PropagationDemo {

	public static void main(String[] args) {
		Universe u = new Universe("a0", "a1", "a2", "b0", "b1", "b2");
		Relation a = Relation.unary("A");
		Relation b = Relation.unary("B");
		Relation ab = Relation.binary("AB");
		Relation ba = Relation.binary("BA");
		Bounds bounds = new Bounds(u);
		bounds.bound(a, u.factory().range(u.factory().tuple("a0"), u.factory().tuple("a2")));
		bounds.bound(b, u.factory().range(u.factory().tuple("b0"), u.factory().tuple("b2")));
		bounds.bound(ab, bounds.upperBound(a).product(bounds.upperBound(b)));
		TupleSet ts = bounds.upperBound(b).product(bounds.upperBound(a));
		ts.removeIf(t -> t.atom(1) != "a0");
		bounds.bound(ba, ts);
		Formula f = ab.join(ba).in(ConstantExpression.IDEN);
		boolean changed = true;
		while (changed) {
			ExpressionBounds eb = new ExpressionBounds(bounds);
			UpwardExpressionBoundPropagator uebp = new UpwardExpressionBoundPropagator(eb);
			f.accept(uebp);
			DownwardExpressionBoundPropagator debp = new DownwardExpressionBoundPropagator(eb);
			f.accept(debp);
			changed = eb.changed();
		}
	}

}
