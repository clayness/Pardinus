package kkpartition.examples;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;

import kkpartition.MProblem;
import kkpartition.PProblem;
import kkpartition.ParallelSolver;
import kkpartition.ParallelSolver.Modes;
import kkpartition.ParallelSolver.Solvers;
import kkpartition.PartitionModel;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.IncrementalSolver;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

public final class RunTestModel {

	final static Solver solver = new Solver();
	final static ParallelSolver psolver = new ParallelSolver(solver);

	static PProblem psolution = null;
	static Solution solution = null;

	static int threads = 4, sym = 20;
	static Solvers selected_solver;
	static Modes selected_mode;

	static PartitionModel model;
	
	static private StringBuilder log = new StringBuilder();

	static private PrintWriter writer;

	/**
	 * Runs a partition problem model defined by the args.
	 * [PartitionModel class, mode, solver, PartitionModel args]
	 * @throws IOException
	 * @throws ClassNotFoundException
	 * @throws SecurityException
	 * @throws NoSuchMethodException
	 * @throws InvocationTargetException
	 * @throws IllegalArgumentException
	 * @throws IllegalAccessException
	 * @throws InstantiationException
	 */
	public static void main(String[] args) throws IOException, InstantiationException, IllegalAccessException,
	IllegalArgumentException, InvocationTargetException, NoSuchMethodException, SecurityException,
	ClassNotFoundException {

		// the arguments for the partition model
		String[] model_args = Arrays.copyOfRange(args, 3, args.length);

		// dynamically create a partition model from the specified class
		model = (PartitionModel) Class.forName(args[0]).getConstructor(String[].class)
				.newInstance((Object) model_args);

		// the chosen partition mode
		selected_mode = Modes.valueOf(args[1]);
		// the chosen solver
		selected_solver = Solvers.valueOf(args[2]);

		writer = new PrintWriter(new FileWriter("pkklog.txt", true));

		run_tests();

		// guarantees that every running thread is terminated.
		System.exit(0);
	}

	/**
	 * Given a partitioned model, runs the model under selected parameters.
	 * 
	 * @param model
	 * @param sym
	 */
	private static void run_tests() {
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();

		solver.options().setBitwidth(model.getBitwidth());
		solver.options().setSymmetryBreaking(sym);

		switch (selected_solver) {
		case GLUCOSE:
			solver.options().setSolver(SATFactory.Glucose);
			break;
		case MINISAT:
			solver.options().setSolver(SATFactory.MiniSat);
			break;
		case PLINGELING:
			solver.options().setSolver(SATFactory.plingeling());
			break;
		case SYRUP:
			solver.options().setSolver(SATFactory.syrup());
			break;
		default:
			break;
		}

		// warm up
//		for (int i = 0; i < 30; i++)
//			solver.solve(f1, b1);

		long t1 = System.currentTimeMillis();

		switch (selected_mode) {
		case BATCH:
			solution = go_batch(b1, b2, f1, f2);
			break;
		case SEQUENTIAL:
			psolver.options().setThreads(1);
			psolver.options().setHybrid(false);
			psolution = psolver.solve(b1, b2, f1, f2);
			break;
		case PARALLEL:
			psolver.options().setThreads(threads);
			psolver.options().setHybrid(false);
			psolution = psolver.solve(b1, b2, f1, f2);
			break;
		case HYBRID:
			psolver.options().setThreads(threads);
			psolver.options().setHybrid(true);
			psolution = psolver.solve(b1, b2, f1, f2);
			break;
		case INCREMENTAL:
			solution = go_incremental(b1, b2, f1, f2);
			break;
		default:
			break;
		}

		long t2 = System.currentTimeMillis();
		log.append((t2 - t1));
		log.append("\t");

		if (selected_mode == Modes.SEQUENTIAL || selected_mode == Modes.PARALLEL || selected_mode == Modes.HYBRID) {
			log.append(psolution.sat() ? "S" : "U");
			log.append("\t");
			log.append(getConfigNum(psolver));
			log.append("\t");
			log.append(getGenTime(psolver));
		} else {
			log.append(solution.sat() ? "S" : "U");
		}
		log.append("\t");

		flush();
	}

	private static void flush() {
		System.out.print(log.toString());
		writer.print(log.toString());
		writer.flush();
		log = new StringBuilder();
	}

	private static long getGenTime(ParallelSolver psolver2) {
		long counter = 0;
		for (PProblem p : psolver2.manager().solutions())
			if (p instanceof MProblem)
				counter = counter + ((MProblem) p).getConfigTime();
		return counter;
	}

	private static int getConfigNum(ParallelSolver psolver2) {
		int counter = psolver2.manager().solutions().size();
		if (counter != 0)
			if (!(psolver2.manager().solutions().get(psolver2.manager().solutions().size() - 1) instanceof MProblem))
				counter = -counter;
		return counter;
	}

	/**
	 * Solves the problem under standard Kodkod (i.e., batch mode).
	 * 
	 * @param b1
	 * @param b2
	 * @param f1
	 * @param f2
	 * @return
	 */
	private static Solution go_batch(Bounds b1, Bounds b2, Formula f1, Formula f2) {
		Bounds b3 = b1.clone();
		for (Relation r : b2.relations()) {
			b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
		}
		return solver.solve(f1.and(f2), b3);
	}

	private static Solution go_incremental(Bounds b1, Bounds b2, Formula f1, Formula f2) {
		IncrementalSolver isolver = IncrementalSolver.solver(solver.options());

		Bounds b3 = b1.clone();
		for (Relation r : b2.relations()) {
			b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
		}
		isolver.solve(f1, b3);
		b3.relations().clear();
		return isolver.solve(f2, b3);

		// isolver.solve(f1,b1);
		// return isolver.solve(f2,b2);
	}

}