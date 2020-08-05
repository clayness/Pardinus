package kodkod.test.pardinus.decomp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Set;

import kodkod.ast.Formula;
import kodkod.engine.DecomposedPardinusSolver;
import kodkod.engine.ExtendedSolver;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.AbstractReporter;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Reporter;
import kodkod.engine.decomp.DModel;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.decomp.HotelP;
import kodkod.examples.pardinus.decomp.HotelP.Variant;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.util.ints.IntSet;

import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.junit.rules.Timeout;
import org.junit.runners.model.TestTimedOutException;

public class HotelTests {
	ExtendedOptions opt;
	
	@Before 
	public void method() throws InterruptedException {
		Reporter rep = new AbstractReporter() {
			@Override
			public void translatingToBoolean(Formula formula, Bounds bounds) {
				System.out.println("to bool: " + formula.toString() + ", "
						+ bounds);
			}
			
			@Override
			public void detectedSymmetries(Set<IntSet> parts) {
				System.out.println("symmetry: " + parts.toString());
			}
			
			@Override
			public void debug(String debug) {
				System.out.println(debug);
			}
		};
		opt = new ExtendedOptions();
		opt.setRunDecomposed(true);
		opt.setSymmetryBreaking(20);
		opt.setSolver(SATFactory.Glucose);
		opt.setDecomposedMode(DMode.PARALLEL);
		opt.setThreads(4);
		opt.setRunTemporal(false);

//		opt.setReporter(rep);
	}
	
	@Rule
    public Timeout globalTimeout = Timeout.seconds(60);
	@Rule
    public final ExpectedException thrown = ExpectedException.none();
	
	@Test 
	public void testSAT3() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setSkolemDepth(-1);
		opt.setRunDecomposed(true);

		PardinusSolver psolver = new PardinusSolver(opt);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();
		
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertEquals(model.shortName()+": #Configs", 20, configs);
		
	}
	
	@Test 
	public void testSAT4() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();

		assertTrue(model.shortName()+": SAT", solution.sat());
		// 75, but decomp launches batches of 50
		assertEquals(model.shortName()+": #Configs", 50, configs);

	}
	
	@Test 
	public void testSAT5() throws InterruptedException {
		int n = 5;
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();

		assertTrue(model.shortName()+": SAT", solution.sat());
		// >200, but decomp launches batches of 50
		assertEquals(model.shortName()+": #Configs", 50, configs);
	}
	
	@Test 
	public void testUNSAT3() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant v1 = Variant.NOINTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();

		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();
		long runs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns();

		assertFalse(model.shortName()+": SAT", solution.sat());
		assertEquals(model.shortName()+": #Runs", 20, runs);
		assertEquals(model.shortName()+": #Configs", 20, configs);
	}
	
	@Test 
	public void testHSAT3() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		opt.setDecomposedMode(DMode.HYBRID);
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();

		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();
		long runs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns();
		boolean amalgamated = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated();

		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", configs <= 20);
		assertTrue(model.shortName()+": #Runs", runs < 20);
		assertFalse(model.shortName()+": Amalg", amalgamated);
	}
	
	@Test 
	public void testHSAT4() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		opt.setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));

		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();
		long runs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns();
		boolean amalgamated = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated();

		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", configs <= 75);
		assertTrue(model.shortName()+": #Runs", runs < 75);
		assertFalse(model.shortName()+": Amalg", amalgamated);
	}
	
	@Test 
	public void testHUNSAT3() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant v1 = Variant.NOINTERVENES;
		opt.setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();
		long runs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns();
		boolean amalgamated = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated();

		assertFalse(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", configs <= 20);
		assertTrue(model.shortName()+": #Runs", runs < 20);
		assertTrue(model.shortName()+": Amalg", amalgamated);
	}
	
	@Test 
	public void testHUNSAT4() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant v1 = Variant.NOINTERVENES;
		opt.setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();
		long runs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns();
		boolean amalgamated = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated();

		assertFalse(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", configs <= 75);
		assertTrue(model.shortName()+": #Runs", runs < 75);
		assertTrue(model.shortName()+": Amalg", amalgamated);
	}

}
