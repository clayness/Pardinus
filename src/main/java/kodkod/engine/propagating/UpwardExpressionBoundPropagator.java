package kodkod.engine.propagating;

import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import kodkod.ast.BinaryExpression;
import kodkod.ast.ConstantExpression;
import kodkod.ast.Decl;
import kodkod.ast.Expression;
import kodkod.ast.IfExpression;
import kodkod.ast.NaryExpression;
import kodkod.ast.UnaryExpression;
import kodkod.instance.TupleSet;

public class UpwardExpressionBoundPropagator extends BoundPropagator {

	public UpwardExpressionBoundPropagator(ExpressionBounds bounds) {
		super(bounds);
	}

	@Override
	public void visit(BinaryExpression binExpr) {
		super.visit(binExpr);
		TupleSet lowers, uppers;
		switch (binExpr.op()) {
		case DIFFERENCE:
			lowers = bounds.lowerBound(binExpr.left()).clone();
			lowers.removeAll(bounds.upperBound(binExpr.right()));
			uppers = bounds.upperBound(binExpr.left()).clone();
			uppers.removeAll(bounds.lowerBound(binExpr.right()));
			bounds.bound(binExpr, lowers, uppers);
			break;
		case INTERSECTION:
			lowers = bounds.lowerBound(binExpr.left()).clone();
			lowers.retainAll(bounds.lowerBound(binExpr.right()));
			uppers = bounds.upperBound(binExpr.left()).clone();
			uppers.retainAll(bounds.upperBound(binExpr.right()));
			bounds.bound(binExpr, lowers, uppers);
			break;
		case JOIN:
			lowers = this.getJoinSet(bounds.lowerBound(binExpr.left()), bounds.lowerBound(binExpr.right()));
			uppers = this.getJoinSet(bounds.upperBound(binExpr.left()), bounds.upperBound(binExpr.right()));
			bounds.bound(binExpr, lowers, uppers);
			break;
		case OVERRIDE:
			//@formatter:off
			lowers = this.getOverrideSet(bounds.lowerBound(binExpr.left()), bounds.lowerBound(binExpr.right()), bounds.upperBound(binExpr.right()));
			uppers = this.getOverrideSet(bounds.upperBound(binExpr.left()), bounds.upperBound(binExpr.right()), bounds.lowerBound(binExpr.right()));
			//@formatter:on
			bounds.bound(binExpr, lowers, uppers);
			break;
		case PRODUCT:
			lowers = bounds.lowerBound(binExpr.left()).product(bounds.lowerBound(binExpr.right()));
			uppers = bounds.upperBound(binExpr.left()).product(bounds.upperBound(binExpr.right()));
			bounds.bound(binExpr, lowers, uppers);
			break;
		case UNION:
			lowers = bounds.lowerBound(binExpr.left()).clone();
			lowers.addAll(bounds.lowerBound(binExpr.right()));
			uppers = bounds.upperBound(binExpr.left()).clone();
			uppers.addAll(bounds.upperBound(binExpr.right()));
			bounds.bound(binExpr, lowers, uppers);
			break;
		default:
			break;
		}
	}

	@Override
	public void visit(ConstantExpression constExpr) {
		super.visit(constExpr);
		TupleSet set;
		if (constExpr == Expression.NONE) {
			set = factory().noneOf(1);
		} else if (constExpr == Expression.UNIV) {
			set = factory().allOf(1);
		} else if (constExpr == Expression.IDEN) {
			//@formatter:off
			set = factory().setOf(IntStream.range(0, bounds.universe().size())
					.mapToObj(bounds.universe()::atom)
					.map(a -> factory().tuple(a, a))
					.collect(Collectors.toList()));
			//@formatter:on
			// } else if (constExpr == Expression.INTS) {
			// set = ????;
		} else {
			bounds.bound(constExpr, factory().noneOf(constExpr.arity()), factory().allOf(constExpr.arity()));
			return;
		}
		bounds.bound(constExpr, set, set);
	}

	@Override
	public void visit(Decl decl) {
		super.visit(decl);
		bounds.bound(decl.variable(), bounds.lowerBound(decl.expression()), bounds.upperBound(decl.expression()));
	}

	@Override
	public void visit(IfExpression ifExpr) {
		super.visit(ifExpr);
		TupleSet lowers = bounds.lowerBound(ifExpr.thenExpr()).clone();
		lowers.retainAll(bounds.lowerBound(ifExpr.elseExpr()));
		TupleSet uppers = bounds.upperBound(ifExpr.thenExpr()).clone();
		uppers.addAll(bounds.upperBound(ifExpr.elseExpr()));
		bounds.bound(ifExpr, lowers, uppers);
	}

	@Override
	public void visit(NaryExpression expr) {
		super.visit(expr);
		TupleSet lowers = null, uppers = null;
		switch (expr.op()) {
		case INTERSECTION:
			lowers = reduce1(expr, bounds::lowerBound, TupleSet::retainAll);
			uppers = reduce1(expr, bounds::upperBound, TupleSet::retainAll);
			bounds.bound(expr, lowers, uppers);
			break;
		case OVERRIDE:
			for (Expression e : expr) {
				if (lowers == null) {
					lowers = bounds.lowerBound(e);
				} else {
					Set<Object> firsts = firsts(bounds.upperBound(e));
					lowers.removeIf(t -> firsts.contains(t.atom(0)));
					lowers.addAll(bounds.lowerBound(e));
				}
				if (uppers == null) {
					uppers = bounds.upperBound(e);
				} else {
					Set<Object> firsts = firsts(bounds.lowerBound(e));
					uppers.removeIf(t -> firsts.contains(t.atom(0)));
					uppers.addAll(bounds.upperBound(e));
				}
			}
			bounds.bound(expr, lowers, uppers);
			break;
		case PRODUCT:
			lowers = reduce2(expr, bounds::lowerBound, TupleSet::product);
			uppers = reduce2(expr, bounds::upperBound, TupleSet::product);
			bounds.bound(expr, lowers, uppers);
			break;
		case UNION:
			lowers = reduce1(expr, bounds::lowerBound, TupleSet::addAll);
			uppers = reduce1(expr, bounds::upperBound, TupleSet::addAll);
			bounds.bound(expr, lowers, uppers);
			break;
		default:
			break;
		}
	}

	@Override
	public void visit(UnaryExpression unaryExpr) {
		super.visit(unaryExpr);
		switch (unaryExpr.op()) {
		//@formatter:off
		case CLOSURE:
			bounds.bound(unaryExpr, 
					this.getClosureSet(bounds.lowerBound(unaryExpr.expression()), false),
					this.getClosureSet(bounds.upperBound(unaryExpr.expression()), false));
			break;
		case REFLEXIVE_CLOSURE:
			bounds.bound(unaryExpr, 
					this.getClosureSet(bounds.lowerBound(unaryExpr.expression()), true),
					this.getClosureSet(bounds.upperBound(unaryExpr.expression()), true));
			break;
		case TRANSPOSE:
			bounds.bound(unaryExpr, 
					this.getTransposeSet(bounds.lowerBound(unaryExpr.expression())),
					this.getTransposeSet(bounds.upperBound(unaryExpr.expression())));
			break;
		default:
			break;
		// @formatter:on
		}
	}

}
