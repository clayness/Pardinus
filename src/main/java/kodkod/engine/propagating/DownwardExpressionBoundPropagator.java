package kodkod.engine.propagating;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import kodkod.ast.BinaryExpression;
import kodkod.ast.BinaryFormula;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.Expression;
import kodkod.ast.IfExpression;
import kodkod.ast.MultiplicityFormula;
import kodkod.ast.NaryExpression;
import kodkod.ast.NaryFormula;
import kodkod.ast.NotFormula;
import kodkod.ast.UnaryExpression;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;

public class DownwardExpressionBoundPropagator extends BoundPropagator {

	public DownwardExpressionBoundPropagator(ExpressionBounds bounds) {
		super(bounds);
	}

	private List<TupleSet> split(NaryExpression expr, TupleSet tuples) {
		List<TupleSet> retval = new ArrayList<>();
		expr.forEach(c -> retval.add(factory().noneOf(c.arity())));
		for (Tuple t : tuples) {
			int i = 0;
			for (int j = 0; j < expr.size(); j++) {
				//@formatter:off
				int k = expr.child(j).arity();
				retval.get(j).add(factory().tuple(IntStream.range(i, i + k)
						.mapToObj(t::atom)
						.collect(Collectors.toList())));
				i += k;
				//@formatter:on
			}
		}
		return retval;
	}

	@Override
	public void visit(BinaryExpression binExpr) {
		TupleSet leftLower, leftUpper, rightLower, rightUpper;
		switch (binExpr.op()) {
		case DIFFERENCE: {
			// what do we know of the lower bounds in this case?
			// - every tuple appearing in the lower bound of the
			// parent can be added to the lower bound of the
			// left child
			leftLower = bounds.lowerBound(binExpr.left()).clone();
			leftLower.addAll(bounds.lowerBound(binExpr));
			// - every tuple in the lower bound of the left child
			// that is NOT in the lower bound of the parent
			// can be added to the lower bound of the right child
			rightLower = bounds.lowerBound(binExpr.right()).clone();
			for (Tuple t : leftLower) {
				if (!bounds.lowerBound(binExpr).contains(t)) {
					rightLower.add(t);
				}
			}
			// what do we know of the upper bounds in this case?
			// - every tuple that appears in the upper bound
			// of the left child but NOT the upper bound
			// of the parent OR the upper bound of the
			// the right child can be removed from the
			// upper bound of the left child
			//@formatter:off
			leftUpper = bounds.upperBound(binExpr.left()).clone();
			leftUpper.removeIf(t -> !bounds.upperBound(binExpr).contains(t) && !bounds.upperBound(binExpr.right()).contains(t));
			//@formatter:on
			// - every tuple that appears in the lower bound
			// of the parent can be removed from the upper
			// bound of the right child
			rightUpper = bounds.upperBound(binExpr.right()).clone();
			rightUpper.removeAll(bounds.lowerBound(binExpr));
			bounds.bound(binExpr.left(), leftLower, leftUpper);
			bounds.bound(binExpr.right(), rightLower, rightUpper);
			break;
		}
		case INTERSECTION: {
			// what do we know of the lower bounds in this case?
			// - every tuple in the lower bound of the parent
			// can be added to the lower bound for each child
			leftLower = bounds.lowerBound(binExpr.left()).clone();
			leftLower.addAll(bounds.lowerBound(binExpr));
			rightLower = bounds.lowerBound(binExpr.right()).clone();
			rightLower.addAll(bounds.lowerBound(binExpr));
			// what do we know of the upper bounds in this case?
			// - ...nothing. we can't adjust upper bounds here
			bounds.bound(binExpr.left(), leftLower, null);
			bounds.bound(binExpr.right(), rightLower, null);
			break;
		}
		case JOIN: {
			// what do we know of the lower bounds in this case?
			// - every tuple in the upper bound of the left child
			// that is the only possible prefix for at least one of
			// the tuples in the lower bound of the parent can
			// be added to the lower bound of the left child
			// (same with the right child and suffixes)
			leftLower = bounds.lowerBound(binExpr.left()).clone();
			rightLower = bounds.lowerBound(binExpr.right()).clone();
			Map<Tuple, List<Tuple>> prefixes = new HashMap<>();
			Map<Tuple, List<Tuple>> suffixes = new HashMap<>();
			TupleSet ts = bounds.lowerBound(binExpr);
			for (Tuple p : bounds.upperBound(binExpr.left())) {
				for (Tuple s : bounds.upperBound(binExpr.right())) {
					//@formatter:off
					Tuple t = factory().tuple(Stream.concat(
								tupleStream(p, 0, p.arity() - 1),
								tupleStream(s, 1, s.arity()))
							.collect(Collectors.toList()));
					//@formatter:on
					if (ts.contains(t)) {
						prefixes.computeIfAbsent(t, k -> new ArrayList<>()).add(p);
						suffixes.computeIfAbsent(t, k -> new ArrayList<>()).add(s);
					}
				}
			}
			prefixes.values().stream().filter(l -> l.size() == 1).forEach(leftLower::addAll);
			suffixes.values().stream().filter(r -> r.size() == 1).forEach(rightLower::addAll);
			// what do we know of the upper bounds in this case?
			// - any tuple in the upper bound of the left child with a prefix
			// not found in the upper bound of the parent can be removed
			// (same w/ suffix and right child)
			//@formatter:off
			Map<Tuple, List<Tuple>> topPreUpper   = subsequence(bounds.upperBound(binExpr), 0, binExpr.left().arity() - 1);
			Map<Tuple, List<Tuple>> topSufUpper   = subsequence(bounds.upperBound(binExpr), binExpr.left().arity() - 1, binExpr.arity());
			Map<Tuple, List<Tuple>> leftPreUpper  = subsequence(bounds.upperBound(binExpr.left()), 0, binExpr.left().arity() - 1);
			Map<Tuple, List<Tuple>> rightSufUpper = subsequence(bounds.upperBound(binExpr.right()), 1, binExpr.right().arity());
			leftUpper = bounds.upperBound(binExpr.left()).clone();
			leftPreUpper.keySet().stream()
				.filter(p -> !topPreUpper.containsKey(p))
				.map(leftPreUpper::get)
				.forEach(leftUpper::removeAll);
			rightUpper = bounds.upperBound(binExpr.right()).clone();
			rightSufUpper.keySet().stream()
				.filter(s -> !topSufUpper.containsKey(s))
				.map(rightSufUpper::get)
				.forEach(rightUpper::removeAll);
			//@formatter:on
			bounds.bound(binExpr.left(), leftLower, leftUpper);
			bounds.bound(binExpr.right(), rightLower, rightUpper);
			break;
		}
		case OVERRIDE: {
			// TODO: figure out what to put here
			break;
		}
		case PRODUCT: {
			// what do we know about the lower bounds in this case?
			// - for every tuple in the lower bound of the parent,
			// its prefix can be added to the lower bound of the left child
			// and its suffix can be added to the lower bound of the right child
			leftLower = bounds.lowerBound(binExpr.left()).clone();
			leftUpper = bounds.upperBound(binExpr.left()).clone();
			rightLower = bounds.lowerBound(binExpr.right()).clone();
			rightUpper = bounds.upperBound(binExpr.right()).clone();
			for (Tuple t : bounds.lowerBound(binExpr)) {
				List<Object> prefix = new ArrayList<>();
				List<Object> suffix = new ArrayList<>();
				for (int i = 0; i < t.arity(); i++) {
					if (i < binExpr.left().arity()) {
						prefix.add(t.atom(i));
					} else {
						suffix.add(t.atom(i));
					}
				}
				leftLower.add(factory().tuple(prefix));
				rightLower.add(factory().tuple(suffix));
			}
			// what do we know about the upper bounds in this case?
			// - every tuple in the upper bound of the left child
			// that is not the prefix of a tuple in the parent can be
			// removed from the upper bound of the left child (same with
			// suffix and right child)
			//@formatter:off
			Set<Tuple> prefixes = bounds.upperBound(binExpr).stream()
					.map(t -> tupleStream(t, 0, binExpr.left().arity()))
					.map(s -> s.collect(Collectors.toList()))
					.map(factory()::tuple)
					.collect(Collectors.toSet());
			Set<Tuple> suffixes = bounds.upperBound(binExpr).stream()
					.map(t -> tupleStream(t, binExpr.left().arity(), binExpr.arity()))
					.map(s -> s.collect(Collectors.toList()))
					.map(factory()::tuple)
					.collect(Collectors.toSet());
			//@formatter:on
			leftUpper.removeIf(t -> !prefixes.contains(t));
			rightUpper.removeIf(t -> !suffixes.contains(t));
			bounds.bound(binExpr.left(), leftLower, leftUpper);
			bounds.bound(binExpr.right(), rightLower, rightUpper);
			break;
		}
		case UNION: {
			// what do we know about the lower bounds in this case?
			// - for every tuple in the lower bound of the parent,
			// if that tuple appears in the upper bound for
			// only one of the children, it must be in the lower
			// bound for that child
			leftLower = bounds.lowerBound(binExpr.left()).clone();
			leftUpper = bounds.upperBound(binExpr.left()).clone();
			rightLower = bounds.lowerBound(binExpr.right()).clone();
			rightUpper = bounds.upperBound(binExpr.right()).clone();
			for (Tuple t : bounds.lowerBound(binExpr)) {
				if (leftUpper.contains(t) && !rightUpper.contains(t))
					leftLower.add(t);
				if (!leftUpper.contains(t) && rightUpper.contains(t))
					rightLower.add(t);
			}
			// what do we know of the upper bounds in this case?
			// - every tuple that is not in the upper bound of the parent
			// can be removed from the upper bounds of the children
			leftUpper.retainAll(bounds.upperBound(binExpr));
			rightUpper.retainAll(bounds.upperBound(binExpr));
			bounds.bound(binExpr.left(), leftLower, leftUpper);
			bounds.bound(binExpr.right(), rightLower, rightUpper);
			break;
		}
		default: {
			break;
		}
		}
		super.visit(binExpr);
	}

	@Override
	public void visit(BinaryFormula binFormula) {
		switch (binFormula.op()) {
		case AND:
			// for conjunctive branches of the formula
			// we can propagate the bounds
			super.visit(binFormula);
			break;
		default:
			// for disjunctive branches (or, if, iff)
			// we cannot; the things we might learn
			// about the bounds may be true in this
			// branch, but may not be true in any
			// other branch
			break;

		}
	}

	@Override
	public void visit(ComparisonFormula compFormula) {
		TupleSet lower, upper;
		switch (compFormula.op()) {
		case EQUALS:
			lower = bounds.lowerBound(compFormula.left()).clone();
			lower.addAll(bounds.lowerBound(compFormula.right()));
			upper = bounds.upperBound(compFormula.left()).clone();
			upper.retainAll(bounds.upperBound(compFormula.right()));
			bounds.bound(compFormula.left(), lower, upper);
			bounds.bound(compFormula.right(), lower, upper);
			break;
		case SUBSET:
			lower = bounds.lowerBound(compFormula.left()).clone();
			lower.addAll(bounds.lowerBound(compFormula.right()));
			upper = bounds.upperBound(compFormula.left()).clone();
			upper.retainAll(bounds.upperBound(compFormula.right()));
			bounds.bound(compFormula.right(), lower, null);
			bounds.bound(compFormula.left(), null, upper);
			break;
		default:
			break;
		}
		super.visit(compFormula);
	}

	@Override
	public void visit(IfExpression ifExpr) {
		// what do we know of the lower bounds in this case?
		// - if a tuple is in the lower bound of the
		// parent, it must be in the lower bound
		// of BOTH of the children
		TupleSet thenLower = bounds.lowerBound(ifExpr.thenExpr()).clone();
		TupleSet thenUpper = bounds.upperBound(ifExpr.thenExpr()).clone();
		TupleSet elseLower = bounds.lowerBound(ifExpr.elseExpr()).clone();
		TupleSet elseUpper = bounds.upperBound(ifExpr.elseExpr()).clone();
		thenLower.addAll(bounds.lowerBound(ifExpr));
		elseLower.addAll(bounds.lowerBound(ifExpr));
		// what do we know of the upper bounds in this case?
		// - nothing for now
		bounds.bound(ifExpr.thenExpr(), thenLower, thenUpper);
		bounds.bound(ifExpr.elseExpr(), elseLower, elseUpper);
		super.visit(ifExpr);
	}

	@Override
	public void visit(MultiplicityFormula multFormula) {
		TupleSet lowers, uppers;
		switch (multFormula.multiplicity()) {
		case NO:
			//@formatter:off
			bounds.bound(multFormula.expression(), 
					factory().noneOf(multFormula.expression().arity()),
					factory().noneOf(multFormula.expression().arity()));
			//@formatter:on
			break;
		case ONE:
		case LONE:
			//@formatter:off
			// what do we know of the lower bounds in this case?
			// - if the inner expression has EXACTLY ONE tuple in its
			// upper bound, then that tuple can be added to the lower bound
			lowers = bounds.lowerBound(multFormula.expression()); 
			uppers = bounds.upperBound(multFormula.expression());
			if (uppers.size() == 1) {
				lowers = uppers;
			// what do we know of the upper bounds in this case?
			// - if the inner expression has EXACTLY ONE tuple in its
			// lower bound, then every other tuple can be removed
			// from the upper bound
			} else if (lowers.size() == 1) {
				uppers = lowers;
			}
			//@formatter:on
			bounds.bound(multFormula.expression(), lowers, uppers);
			break;
		case SOME:
			// what do we know of the lower bounds in this case?
			// - if the inner expression has EXACTLY ONE tuple in its
			// upper bound, then that tuple can be added to the lower bound
			// what do we know of the upper bounds in this case?
			// - nothing. there is no constraint on the upper bound
			uppers = bounds.upperBound(multFormula.expression());
			if (uppers.size() == 1) {
				bounds.bound(multFormula.expression(), uppers, uppers);
			}
			break;
		default:
			// we can't propagate any bounds based on the other multiplicities
			break;
		}
		super.visit(multFormula);
	}

	@Override
	public void visit(NaryExpression expr) {
		TupleSet topLower = bounds.lowerBound(expr);
		TupleSet topUpper = bounds.upperBound(expr);
		switch (expr.op()) {
		case INTERSECTION:
			// what do we know of the lower bound in this case?
			// - the lower bound of the parent can be added to
			// the lower bound of each of the children
			for (Expression child : expr) {
				TupleSet lowers = bounds.lowerBound(child).clone();
				lowers.addAll(topLower);
				bounds.bound(child, lowers, null);
			}
			// what do we know of the upper bound in this case?
			// - nothing. we cannot adjust upper bounds via intersection
			break;
		case OVERRIDE:
			// what do we know of the lower bound in this case?
			// what do we know of the upper bound in this case?
			break;
		case PRODUCT:
			// what do we know of the lower bound in this case?
			// - the sets representing the corresponding subsequences
			// of the lower bound can be added to the lower bound
			// for each child
			// what do we know of the upper bound in this case?
			// - each tuple in each child that does not match
			// the corresponding subsequence of at least one
			// tuple in the upper bound of the parent can be
			// removed from the corresponding child
			List<TupleSet> loSplits = split(expr, topLower);
			List<TupleSet> hiSplits = split(expr, topUpper);
			for (int i = 0; i < expr.size(); i++) {
				Expression child = expr.child(i);
				TupleSet loSplit = loSplits.get(i);
				TupleSet hiSplit = hiSplits.get(i);
				TupleSet lowers = bounds.lowerBound(child).clone();
				lowers.addAll(loSplit);
				TupleSet uppers = bounds.upperBound(child).clone();
				uppers.removeIf(t -> !hiSplit.contains(t));
				bounds.bound(child, lowers, uppers);
			}
			break;
		case UNION:
			// what do we know of the lower bound in this case?
			// - any tuple in the lower bound of the parent that
			// appears in EXACTLY ONE of the upper bounds of the
			// children can be added to the lower bound of that child
			// what do we know of the upper bound in this case?
			// - any tuple in any of the upper bounds of the children
			// that does not appear in the upper bound of the parent
			// can be removed from the upper bound of that child
			Set<Tuple> singletons = topLower.stream().filter(t -> IntStream.range(0, expr.size()).mapToObj(expr::child)
					.map(bounds::upperBound).filter(c -> c.contains(t)).count() == 1).collect(Collectors.toSet());
			for (Expression child : expr) {
				TupleSet lowers = bounds.lowerBound(child).clone();
				TupleSet uppers = bounds.upperBound(child).clone();
				uppers.removeIf(t -> !topUpper.contains(t));
				for (Tuple t : uppers) {
					if (singletons.contains(t)) {
						lowers.add(t);
					}
				}
				bounds.bound(child, lowers, uppers);
			}
			break;
		default:
			break;
		}
		super.visit(expr);
	}

	@Override
	public void visit(NaryFormula naryFormula) {
		switch (naryFormula.op()) {
		case AND:
			// for conjunctive branches of the formula
			// we can propagate the bounds
			super.visit(naryFormula);
			break;
		default:
			// for disjunctive branches (or, if, iff)
			// we cannot; the things we might learn
			// about the bounds may be true in this
			// branch, but may not be true in any
			// other branch
			break;

		}
	}

	@Override
	public void visit(NotFormula notFormula) {
		// stop once we hit the first not formula,
		// nothing we can guarantee about negations
	}

	@Override
	public void visit(UnaryExpression unaryExpr) {
		switch (unaryExpr.op()) {
		case CLOSURE:
			// what do we know about the lower bounds here?
			// what do we know about the upper bounds here?
			break;
		case REFLEXIVE_CLOSURE:
			// what do we know about the lower bounds here?
			// what do we know about the upper bounds here?
			break;
		case TRANSPOSE:
			//@formatter:off
			bounds.bound(unaryExpr.expression(), 
					this.getTransposeSet(bounds.lowerBound(unaryExpr)),
					this.getTransposeSet(bounds.upperBound(unaryExpr)));
			//@formatter:on
			break;
		default:
			break;
		}
		super.visit(unaryExpr);
	}

}
