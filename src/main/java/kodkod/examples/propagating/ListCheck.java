/* 
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.examples.propagating;

import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.propagating.DownwardExpressionBoundPropagator;
import kodkod.engine.propagating.ExpressionBounds;
import kodkod.engine.propagating.UpwardExpressionBoundPropagator;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.propagating.ListViz.State;
import kodkod.instance.Bounds;

/**
 * Bounded verification demo.
 * 
 * @author Emina Torlak
 *
 */
public class ListCheck extends ListEncoding {

	ListCheck() {
	}

	Formula checkSpec() {
		return Formula.and(pre(), loopGuard(), post().not());
	}

	Bounds checkBounds(int size) {
		return bounds(size);
	}

	Solution check(int size) {
		final Solver solver = new Solver();
		solver.options().setSolver(SATFactory.MiniSat);
		Formula spec = checkSpec();
		Bounds bounds = checkBounds(size);

		boolean changed = true;
		while (changed) {
			ExpressionBounds eb = new ExpressionBounds(bounds);
			UpwardExpressionBoundPropagator uebp = new UpwardExpressionBoundPropagator(eb);
			spec.accept(uebp);
			DownwardExpressionBoundPropagator debp = new DownwardExpressionBoundPropagator(eb);
			spec.accept(debp);
			changed = eb.changed();
		}
		return solver.solve(spec, bounds);
	}

	private void showCheck(int size) {
		final Solution sol = check(size);
		System.out.println("************ CHECK REVERSE FOR " + size + " NODES ************");
		System.out.println(sol.outcome());
		System.out.println();
		System.out.println(sol.stats());
		System.out.println();
		ListViz.printInstance(this, sol.instance());
		ListViz.printStateGraph("check-pre", this, sol.instance(), State.PRE);
		ListViz.printStateGraph("check-post", this, sol.instance(), State.POST);
	}

	public static void main(String[] args) throws IOException {
		Path path = Paths.get("log", "bounds.out");
		if (!Files.exists(path.getParent()))
			Files.createDirectories(path.getParent());
		try (PrintStream out = new PrintStream(Files.newOutputStream(path))) {
			System.setOut(out);
			ListCheck enc = new ListCheck();
			// ListViz.printEncoding(enc);
			// enc.showCheck(1);
			// enc.showCheck(2);
			enc.showCheck(3);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
