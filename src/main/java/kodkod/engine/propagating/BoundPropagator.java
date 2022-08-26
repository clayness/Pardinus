package kodkod.engine.propagating;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import kodkod.ast.Expression;
import kodkod.ast.Node;
import kodkod.ast.visitor.AbstractVoidVisitor;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;

public abstract class BoundPropagator extends AbstractVoidVisitor {
	private final Set<Node> cache = new HashSet<>();
	protected final ExpressionBounds bounds;

	protected BoundPropagator(ExpressionBounds bounds) {
		this.bounds = bounds;
	}

	@Override
	protected boolean visited(Node n) {
		return !cache.add(n);
	}

	/**
	 * Helper method to return the factory for this propagator's universe.
	 * 
	 * @return
	 */
	protected TupleFactory factory() {
		return bounds.universe().factory();
	}

	/**
	 * Returns a set containing the first atoms of all the tuples in the passed set.
	 * Used for computing the bounds for the override (++) operator.
	 * 
	 * @param ts
	 * @return
	 */
	protected Set<Object> firsts(TupleSet ts) {
		return ts.stream().map(t -> t.atom(0)).collect(Collectors.toSet());
	}

	/**
	 * Returns the (reflexive) transitive closure of the passed set of binary
	 * tuples.
	 * 
	 * @param inner
	 * @param reflexive
	 * @return
	 */
	protected TupleSet getClosureSet(TupleSet inner, boolean reflexive) {
		TupleSet retval = inner.clone();
		if (reflexive) {
			for (Tuple t : inner) {
				retval.add(factory().tuple(t.atom(0), t.atom(0)));
				retval.add(factory().tuple(t.atom(1), t.atom(1)));
			}
		}
		Map<Object, List<Tuple>> firsts = new HashMap<>();
		for (Tuple t : inner) {
			firsts.computeIfAbsent(t.atom(0), k -> new ArrayList<>()).add(t);
		}
		boolean added = true;
		while (added) {
			added = false;
			TupleSet temp = factory().noneOf(retval.arity());
			for (Tuple t : retval) {
				for (Tuple r : firsts.getOrDefault(t.atom(1), Collections.emptyList())) {
					Tuple s = factory().tuple(t.atom(0), r.atom(1));
					if (!retval.contains(s)) {
						temp.add(s);
						firsts.computeIfAbsent(s.atom(0), k -> new ArrayList<>()).add(s);
						added = true;
					}
				}
			}
			if (added) {
				retval.addAll(temp);
			}
		}
		return retval;
	}

	/**
	 * Returns the result of joining the passed tuple sets.
	 * 
	 * @param left
	 * @param right
	 * @return
	 */
	protected TupleSet getJoinSet(TupleSet left, TupleSet right) {
		Map<Object, List<Tuple>> firsts = right.stream().collect(Collectors.groupingBy(t -> t.atom(0)));
		List<Tuple> tuples = new ArrayList<>();
		for (Tuple t : left) {
			for (Tuple r : firsts.getOrDefault(t.atom(t.arity() - 1), Collections.emptyList())) {
				//@formatter:off
				tuples.add(factory().tuple(Stream.concat(
							tupleStream(t, 0, t.arity() - 1), 
							tupleStream(r, 1, r.arity()))
						.collect(Collectors.toList())));
				//@formatter:on
			}
		}
		return tuples.isEmpty() ? factory().noneOf(left.arity() + right.arity() - 2) : factory().setOf(tuples);
	}

	/**
	 * Returns a bound for the override operator (++). Formally, this method
	 * returns: overrider + { t : (t in overridee) and (no u in guaranteedOverrides
	 * : u[0] == t[0]) }
	 *
	 * @param overridee
	 * @param overrider
	 * @param guaranteedOverrides
	 * @return
	 */
	protected TupleSet getOverrideSet(TupleSet overridee, TupleSet overrider, TupleSet guaranteedOverrides) {
		Set<Object> firsts = firsts(guaranteedOverrides);
		TupleSet retval = overridee.clone();
		retval.removeIf(t -> firsts.contains(t.atom(0)));
		retval.addAll(overrider);
		return retval;
	}

	/**
	 * Returns the transpose of the passed tuple set (i.e., reversing the atoms of
	 * each tuple)
	 * 
	 * @param inner
	 * @return
	 */
	protected TupleSet getTransposeSet(TupleSet inner) {
		//@formatter:off
		List<Tuple> tuples = inner.stream()
				.map(t -> factory().tuple(IntStream.range(0, t.arity())
						.map(i -> t.arity() - i - 1)
						.mapToObj(t::atom)
						.collect(Collectors.toList())))
				.collect(Collectors.toList());
		//@formatter:on
		return tuples.isEmpty() ? factory().noneOf(inner.arity()) : factory().setOf(tuples);
	}

	/**
	 * Helper method to apply the passed void method (lambda2) to each member of the
	 * passed iterable, ultimately returning the modified result. Used for computing
	 * bounds for n-ary operations.
	 * 
	 * @param iterable
	 * @param lambda1
	 * @param lambda2
	 * @return
	 */
	protected TupleSet reduce1(Iterable<Expression> iterable, Function<Expression, TupleSet> lambda1,
			BiConsumer<TupleSet, TupleSet> lambda2) {
		TupleSet l = null;
		Iterator<Expression> it = iterable.iterator();
		if (it.hasNext()) {
			l = lambda1.apply(it.next()).clone();
		}
		while (it.hasNext()) {
			lambda2.accept(l, lambda1.apply(it.next()));
		}
		return l;
	}

	/**
	 * Helper method to apply the passed function (lambda2) to each member of the
	 * passed iterable, returning the result of the last application. Used for
	 * computing bounds for n-ary operations.
	 * 
	 * @param iterable
	 * @param lambda1
	 * @param lambda2
	 * @return
	 */
	protected TupleSet reduce2(Iterable<Expression> iterable, Function<Expression, TupleSet> lambda1,
			BiFunction<TupleSet, TupleSet, TupleSet> lambda2) {
		TupleSet l = null;
		Iterator<Expression> it = iterable.iterator();
		if (it.hasNext()) {
			l = lambda1.apply(it.next());
		}
		while (it.hasNext()) {
			l = lambda2.apply(l, lambda1.apply(it.next()));
		}
		return l;
	}

	/**
	 * Helper method to turn a tuple (or subsequence within a tuple) into a stream.
	 * 
	 * @param t
	 * @param s
	 * @param e
	 * @return
	 */
	protected Stream<Object> tupleStream(Tuple t, int s, int e) {
		return IntStream.range(s, e).mapToObj(t::atom);
	}

	protected Map<Tuple, List<Tuple>> subsequence(TupleSet src, int l, int r) {
		Map<Tuple, List<Tuple>> retval = new HashMap<>();
		for (Tuple t : src) {
			List<Object> subseq = new ArrayList<>();
			for (int i = l; i < r; i++) {
				subseq.add(t.atom(i));
			}
			if (!subseq.isEmpty()) {
				retval.computeIfAbsent(factory().tuple(subseq), k -> new ArrayList<>()).add(t);
			}
		}
		return retval;
	}
}
