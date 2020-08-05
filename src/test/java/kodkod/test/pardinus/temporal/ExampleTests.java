package kodkod.test.pardinus.temporal;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.junit.rules.Timeout;
import org.junit.runners.model.TestTimedOutException;

import kodkod.ast.Formula;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.SLF4JReporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.temporal.HotelT;
import kodkod.examples.pardinus.temporal.HotelT.Variant;
import kodkod.instance.PardinusBounds;

public class ExampleTests {
	
	public final ExtendedOptions options;
	
	public ExampleTests() {
		options = new ExtendedOptions();
		options.setRunTemporal(true);
		options.setRunDecomposed(false);
		options.setMaxTraceLength(10);
//		options.setReporter(new SLF4JReporter());
	}
	
	@Rule
    public Timeout globalTimeout = Timeout.seconds(60);
	@Rule
    public final ExpectedException thrown = ExpectedException.none();
	
	@Test
	public void testSATBounded() {
		options.setRunUnbounded(false);
		options.setSolver(SATFactory.MiniSat);
		HotelT model = new HotelT(new String[] {"2",Variant.INTERVENES.toString()} );
		Formula formula = model.formula();
		PardinusBounds bounds = model.bounds();
		PardinusSolver solver = new PardinusSolver(options);
		Solution sol = solver.solve(formula, bounds);
		assert(sol.sat());
	}

	@Test
	public void testUNSATLengthBounded() {
		options.setRunUnbounded(false);
		options.setSolver(SATFactory.MiniSat);
		options.setMaxTraceLength(3);
		HotelT model = new HotelT(new String[] {"2",Variant.INTERVENES.toString()} );
		Formula formula = model.formula();
		PardinusBounds bounds = model.bounds();
		PardinusSolver solver = new PardinusSolver(options);
		Solution sol = solver.solve(formula, bounds);
		assert(!sol.sat());
	}

	@Test
	public void testUNSATFormulaBounded() {
		options.setRunUnbounded(false);
		options.setSolver(SATFactory.MiniSat);
		HotelT model = new HotelT(new String[] {"2",Variant.NOINTERVENES.toString()} );
		Formula formula = model.formula();
		PardinusBounds bounds = model.bounds();
		PardinusSolver solver = new PardinusSolver(options);
		Solution sol = solver.solve(formula, bounds);
		assert(!sol.sat());
	}
	
	// NuSMV times out
	@Test(expected = TestTimedOutException.class)
	public void testSATComplete() {
		thrown.expect(TestTimedOutException.class);
		options.setRunUnbounded(true);
		options.setSolver(SATFactory.electrod("-t","NuSMV"));
		HotelT model = new HotelT(new String[] {"1",Variant.INTERVENES.toString()} );
		Formula formula = model.formula();
		PardinusBounds bounds = model.bounds();
		PardinusSolver solver = new PardinusSolver(options);
		Solution sol = solver.solve(formula, bounds);
		assert(sol.sat());
	}

	// NuSMV times out
	@Test(expected = TestTimedOutException.class)
	public void testUNSATFormulaComplete() {
		thrown.expect(TestTimedOutException.class);
		options.setRunUnbounded(true);
		options.setSolver(SATFactory.electrod("-t","NuSMV"));
		HotelT model = new HotelT(new String[] {"1",Variant.NOINTERVENES.toString()} );
		Formula formula = model.formula();
		PardinusBounds bounds = model.bounds();
		PardinusSolver solver = new PardinusSolver(options);
		Solution sol = solver.solve(formula, bounds);
		assert(!sol.sat());
	}
	
}
