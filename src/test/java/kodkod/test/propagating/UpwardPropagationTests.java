package kodkod.test.propagating;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import kodkod.ast.Expression;
import kodkod.ast.Relation;
import kodkod.engine.propagating.ExpressionBounds;
import kodkod.engine.propagating.UpwardExpressionBoundPropagator;
import kodkod.instance.Bounds;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

public class UpwardPropagationTests {

	@Test
	public void testTranspose() {
		Universe u = new Universe("a", "b", "c", "d");
		Relation r = Relation.binary("r");
		Bounds b = new Bounds(u);
		TupleSet lower = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"));
		TupleSet upper = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"),
				u.factory().tuple("c", "d"));
		b.bound(r, lower, upper);
		ExpressionBounds eb = new ExpressionBounds(b);
		UpwardExpressionBoundPropagator uut = new UpwardExpressionBoundPropagator(eb);
		Expression f = r.transpose();
		f.accept(uut);
		TupleSet expLower = u.factory().setOf(u.factory().tuple("b", "a"), u.factory().tuple("c", "b"));
		TupleSet expUpper = u.factory().setOf(u.factory().tuple("b", "a"), u.factory().tuple("c", "b"),
				u.factory().tuple("d", "c"));
		assertEquals(expLower, eb.lowerBound(f));
		assertEquals(expUpper, eb.upperBound(f));
	}

	@Test
	public void testTransitiveClosure() {
		Universe u = new Universe("a", "b", "c", "d");
		Relation r = Relation.binary("r");
		Bounds b = new Bounds(u);
		TupleSet lower = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"));
		TupleSet upper = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"),
				u.factory().tuple("c", "d"));
		b.bound(r, lower, upper);
		ExpressionBounds eb = new ExpressionBounds(b);
		UpwardExpressionBoundPropagator uut = new UpwardExpressionBoundPropagator(eb);
		Expression f = r.closure();
		f.accept(uut);
		TupleSet expLower = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"),
				u.factory().tuple("a", "c"));
		TupleSet expUpper = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"),
				u.factory().tuple("c", "d"), u.factory().tuple("a", "c"), u.factory().tuple("a", "d"),
				u.factory().tuple("b", "d"));
		assertEquals(expLower, eb.lowerBound(f));
		assertEquals(expUpper, eb.upperBound(f));
	}

	@Test
	public void testReflexiveClosure() {
		Universe u = new Universe("a", "b", "c", "d");
		Relation r = Relation.binary("r");
		Bounds b = new Bounds(u);
		TupleSet lower = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"));
		TupleSet upper = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"),
				u.factory().tuple("c", "d"));
		b.bound(r, lower, upper);
		ExpressionBounds eb = new ExpressionBounds(b);
		UpwardExpressionBoundPropagator uut = new UpwardExpressionBoundPropagator(eb);
		Expression f = r.reflexiveClosure();
		f.accept(uut);
		TupleSet expLower = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"),
				u.factory().tuple("a", "c"), u.factory().tuple("a", "a"), u.factory().tuple("b", "b"),
				u.factory().tuple("c", "c"));
		TupleSet expUpper = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"),
				u.factory().tuple("c", "d"), u.factory().tuple("a", "c"), u.factory().tuple("a", "d"),
				u.factory().tuple("b", "d"), u.factory().tuple("a", "a"), u.factory().tuple("b", "b"),
				u.factory().tuple("c", "c"), u.factory().tuple("d", "d"));
		assertEquals(expLower, eb.lowerBound(f));
		assertEquals(expUpper, eb.upperBound(f));
	}
	
	@Test
	public void testUnion() {
		Universe u = new Universe("a", "b", "c", "d");
		Bounds b = new Bounds(u);
		Relation r1 = Relation.binary("r1");
		TupleSet lower1 = u.factory().setOf(u.factory().tuple("a", "b"));
		TupleSet upper1 = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"));
		b.bound(r1, lower1, upper1);
		Relation r2 = Relation.binary("r2");
		TupleSet lower2 = u.factory().setOf(u.factory().tuple("a", "a"), u.factory().tuple("a", "b"));
		TupleSet upper2 = u.factory().setOf(u.factory().tuple("a", "a"), u.factory().tuple("a", "b"), u.factory().tuple("b","b"), u.factory().tuple("b","c"));
		b.bound(r2, lower2, upper2);
		ExpressionBounds eb = new ExpressionBounds(b);
		UpwardExpressionBoundPropagator uut = new UpwardExpressionBoundPropagator(eb);
		Expression f = r1.union(r2);
		f.accept(uut);
		TupleSet expLower = u.factory().setOf(
				u.factory().tuple("a", "a"), 
				u.factory().tuple("a", "b"));
		TupleSet expUpper = u.factory().setOf(
				u.factory().tuple("a", "a"),
				u.factory().tuple("a", "b"),
				u.factory().tuple("b", "b"), 
				u.factory().tuple("b", "c"));
		assertEquals(expLower, eb.lowerBound(f));
		assertEquals(expUpper, eb.upperBound(f));
	}
	
	@Test
	public void testIntersection() {
		Universe u = new Universe("a", "b", "c", "d");
		Bounds b = new Bounds(u);
		Relation r1 = Relation.binary("r1");
		TupleSet lower1 = u.factory().setOf(u.factory().tuple("a", "b"));
		TupleSet upper1 = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"));
		b.bound(r1, lower1, upper1);
		Relation r2 = Relation.binary("r2");
		TupleSet lower2 = u.factory().setOf(u.factory().tuple("a", "a"), u.factory().tuple("a", "b"));
		TupleSet upper2 = u.factory().setOf(u.factory().tuple("a", "a"), u.factory().tuple("a", "b"), u.factory().tuple("b","b"), u.factory().tuple("b","c"));
		b.bound(r2, lower2, upper2);
		ExpressionBounds eb = new ExpressionBounds(b);
		UpwardExpressionBoundPropagator uut = new UpwardExpressionBoundPropagator(eb);
		Expression f = r1.intersection(r2);
		f.accept(uut);
		TupleSet expLower = u.factory().setOf(
				u.factory().tuple("a", "b"));
		TupleSet expUpper = u.factory().setOf(
				u.factory().tuple("a", "b"),
				u.factory().tuple("b", "c"));
		assertEquals(expLower, eb.lowerBound(f));
		assertEquals(expUpper, eb.upperBound(f));
	}
	
	@Test
	public void testDifference() {
		Universe u = new Universe("a", "b", "c", "d");
		Bounds b = new Bounds(u);
		Relation r1 = Relation.binary("r1");
		TupleSet lower1 = u.factory().setOf(u.factory().tuple("a", "b"));
		TupleSet upper1 = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"));
		b.bound(r1, lower1, upper1);
		Relation r2 = Relation.binary("r2");
		TupleSet lower2 = u.factory().setOf(u.factory().tuple("a", "a"), u.factory().tuple("a", "b"));
		TupleSet upper2 = u.factory().setOf(u.factory().tuple("a", "a"), u.factory().tuple("a", "b"), u.factory().tuple("b","b"));
		b.bound(r2, lower2, upper2);
		ExpressionBounds eb = new ExpressionBounds(b);
		UpwardExpressionBoundPropagator uut = new UpwardExpressionBoundPropagator(eb);
		Expression f = r1.difference(r2);
		f.accept(uut);
		TupleSet expLower = u.factory().noneOf(2);
		TupleSet expUpper = u.factory().setOf(
				u.factory().tuple("b", "c"));
		assertEquals(expLower, eb.lowerBound(f));
		assertEquals(expUpper, eb.upperBound(f));
	}
	
	@Test
	public void testProduct() {
		Universe u = new Universe("a", "b", "c", "d");
		Bounds b = new Bounds(u);
		Relation r1 = Relation.binary("r1");
		TupleSet lower1 = u.factory().setOf(u.factory().tuple("a", "b"));
		TupleSet upper1 = u.factory().setOf(u.factory().tuple("a", "b"), u.factory().tuple("b", "c"));
		b.bound(r1, lower1, upper1);
		Relation r2 = Relation.binary("r2");
		TupleSet lower2 = u.factory().setOf(u.factory().tuple("a", "a"), u.factory().tuple("a", "b"));
		TupleSet upper2 = u.factory().setOf(u.factory().tuple("a", "a"), u.factory().tuple("a", "b"), u.factory().tuple("b","b"), u.factory().tuple("b","c"));
		b.bound(r2, lower2, upper2);
		ExpressionBounds eb = new ExpressionBounds(b);
		UpwardExpressionBoundPropagator uut = new UpwardExpressionBoundPropagator(eb);
		Expression f = r1.product(r2);
		f.accept(uut);
		TupleSet expLower = u.factory().setOf(
				u.factory().tuple("a","b","a","a"), 
				u.factory().tuple("a","b","a","b"));
		TupleSet expUpper = u.factory().setOf(
				u.factory().tuple("a","b","a","a"),
				u.factory().tuple("a","b","a","b"),
				u.factory().tuple("a","b","b","b"),
				u.factory().tuple("a","b","b","c"),
				u.factory().tuple("b","c","a","a"),
				u.factory().tuple("b","c","a","b"),
				u.factory().tuple("b","c","b","b"),
				u.factory().tuple("b","c","b","c"));
		assertEquals(expLower, eb.lowerBound(f));
		assertEquals(expUpper, eb.upperBound(f));
	}
	
	@Test
	public void testOverride() {
		Universe u = new Universe("a", "b", "c", "d");
		Bounds b = new Bounds(u);
		Relation r1 = Relation.binary("r1");
		TupleSet lower1 = u.factory().setOf(
				u.factory().tuple("a","b"),  // will be overridden by (a,c) from upper bound
				u.factory().tuple("c","c"),  // will not be overridden; no (c,x) in upper bound
				u.factory().tuple("b","d")); // will be overridden by (b,b) from upper bound
		TupleSet upper1 = u.factory().setOf(
				u.factory().tuple("a","b"),  // will be overridden by (a,c) from lower bound 
				u.factory().tuple("b","c"),  // will not be overridden
				u.factory().tuple("b","d"),  // will not be overridden
				u.factory().tuple("c","c")); // will not be overridden
		b.bound(r1, lower1, upper1);
		Relation r2 = Relation.binary("r2");
		TupleSet lower2 = u.factory().setOf(
				u.factory().tuple("a","c"));
		TupleSet upper2 = u.factory().setOf(
				u.factory().tuple("a","c"), 
				u.factory().tuple("b","b"));
		b.bound(r2, lower2, upper2);
		ExpressionBounds eb = new ExpressionBounds(b);
		UpwardExpressionBoundPropagator uut = new UpwardExpressionBoundPropagator(eb);
		Expression f = r1.override(r2);
		f.accept(uut);
		TupleSet expLower = u.factory().setOf(
				u.factory().tuple("a","c"),
				u.factory().tuple("c","c"));
		TupleSet expUpper = u.factory().setOf(
				u.factory().tuple("a","c"),
				u.factory().tuple("b","b"),
				u.factory().tuple("b","c"),
				u.factory().tuple("b","d"),
				u.factory().tuple("c","c"));
		assertEquals(expLower, eb.lowerBound(f));
		assertEquals(expUpper, eb.upperBound(f));
	}
	
	@Test
	public void testJoin() {
		Universe u = new Universe("a", "b", "c", "d");
		Bounds b = new Bounds(u);
		Relation r1 = Relation.binary("r1");
		TupleSet lower1 = u.factory().setOf(
				u.factory().tuple("a","a"), // joins to (a,c)  
				u.factory().tuple("a","b"),  
				u.factory().tuple("c","c"), 
				u.factory().tuple("b","d")); 
		TupleSet upper1 = u.factory().setOf(
				u.factory().tuple("a","a"), // joins to (a,c)  
				u.factory().tuple("a","b"), // joins to (b,b)    
				u.factory().tuple("b","c"),  
				u.factory().tuple("b","d"),
				u.factory().tuple("c","b"), // joins to (b,b)  
				u.factory().tuple("c","c")); 
		b.bound(r1, lower1, upper1);
		Relation r2 = Relation.binary("r2");
		TupleSet lower2 = u.factory().setOf(
				u.factory().tuple("a","c"));
		TupleSet upper2 = u.factory().setOf(
				u.factory().tuple("a","c"), 
				u.factory().tuple("b","b"));
		b.bound(r2, lower2, upper2);
		ExpressionBounds eb = new ExpressionBounds(b);
		UpwardExpressionBoundPropagator uut = new UpwardExpressionBoundPropagator(eb);
		Expression f = r1.join(r2);
		f.accept(uut);
		TupleSet expLower = u.factory().setOf(
				u.factory().tuple("a","c"));
		TupleSet expUpper = u.factory().setOf(
				u.factory().tuple("a","b"),
				u.factory().tuple("a","c"),
				u.factory().tuple("c","b"));
		assertEquals(expLower, eb.lowerBound(f));
		assertEquals(expUpper, eb.upperBound(f));
	}

}
