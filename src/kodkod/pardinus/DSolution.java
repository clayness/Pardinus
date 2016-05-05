package kodkod.pardinus;

import java.util.List;

import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;

/**
 * A decomposed model finding problem.
 * @author nmm
 *
 */
public class DSolution extends Thread {

	public static DSolution DONE = new DSolution(null, null, null);
	final private Solver solver;
	
	private Solution solution;
	final public List<Bounds> bounds;
	final public Formula formula;
	final public DProblemManager manager;

	public DSolution(DProblemManager manager, Formula formula, List<Bounds> bnds) {
		this.manager = manager;
		if (this.manager != null) {
			solver = new Solver(this.manager.solver().options());
			this.bounds = bnds;
			this.formula = formula;
		} else {
			this.solver = null;
			this.formula = null;
			this.bounds = null;
		}
	}

	public void run() {
//		System.out.println("started: "+Thread.currentThread().getId());
		while (!bounds.isEmpty() && (solution == null || !solution.sat())) {
			solution = solver.solve(formula,bounds.remove(0));
		}
		solver.free();
//		System.out.println("ended1: "+Thread.currentThread().getId()+", "+Thread.currentThread().isInterrupted());
		if (!Thread.currentThread().isInterrupted()) manager.end(this);
//		System.out.println("ended2: "+Thread.currentThread().getId());
	}

	public boolean sat() {
		if (solution == null) return false;
		return solution.sat();
	}

	public Solution getSolution() {
		return solution;
	}

	public long getSolveTime() {
		if (solution == null) return -1;
		return solution.stats().solvingTime()+solution.stats().translationTime();
	}

	public String toString() {
		if (solution==null) return "B: UNSOLVED";
		return "B: "+solution.outcome() + "\t" + getSolveTime();
	}
	
}