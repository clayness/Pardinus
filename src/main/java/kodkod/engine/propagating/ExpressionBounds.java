package kodkod.engine.propagating;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

import kodkod.ast.Expression;
import kodkod.ast.Relation;
import kodkod.instance.Bounds;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

public class ExpressionBounds {

	private boolean changed = false;

	private final Bounds bounds;
	private final Map<Expression, TupleSet> lowers = new HashMap<>();
	private final Map<Expression, TupleSet> uppers = new HashMap<>();

	public ExpressionBounds(Bounds bounds) {
		this.bounds = bounds;
	}

	public TupleSet lowerBound(Expression expr) {
		TupleSet retval;
		if (expr instanceof Relation) {
			retval = this.lowers.getOrDefault(expr, this.bounds.lowerBound((Relation) expr));
		} else {
			retval = this.lowers.getOrDefault(expr, null);
		}
		return retval == null ? bounds.universe().factory().noneOf(expr.arity()) : retval;
	}

	public TupleSet upperBound(Expression expr) {
		TupleSet retval;
		if (expr instanceof Relation) {
			retval = this.uppers.getOrDefault(expr, this.bounds.upperBound((Relation) expr));
		} else {
			retval = this.uppers.getOrDefault(expr, null);
		}
		return retval == null ? bounds.universe().factory().allOf(expr.arity()) : retval;
	}

	public void bound(Expression expr, TupleSet lowerBound, TupleSet upperBound) {
		TupleSet currentLower = this.lowerBound(expr);
		TupleSet currentUpper = this.upperBound(expr);
		if (lowerBound == null)
			lowerBound = currentLower;
		if (upperBound == null)
			upperBound = currentUpper;
		if (currentLower != null && currentLower.size() > lowerBound.size()) {
			System.err.println("attempting to shrink lower bound: " + expr.toString());
			return;
		}
		if (currentUpper != null && currentUpper.size() < upperBound.size()) {
			System.err.println("attempting to expand upper bound: " + expr.toString());
			return;
		}
		if ((!Objects.equals(currentLower, lowerBound) || !Objects.equals(currentUpper, upperBound))) {
			if (expr instanceof Relation) {
				this.bounds.bound((Relation) expr, lowerBound, upperBound);
				System.err.println("changing: " + expr.toString());
				System.err.printf("  l: %s -> %s%n", currentLower == null ? "(null)" : currentLower.toString(),
						lowerBound == null ? "(null)" : lowerBound.toString());
				System.err.printf("  u: %s -> %s%n", currentUpper == null ? "(null)" : currentUpper.toString(),
						upperBound == null ? "(null)" : upperBound.toString());
				this.changed = true;
			} else {
				this.lowers.put(expr, lowerBound);
				this.uppers.put(expr, upperBound);
			}
		}
	}

	public void reset() {
		this.changed = false;
	}

	public boolean changed() {
		return this.changed;
	}

	public Universe universe() {
		return this.bounds.universe();
	}
}
