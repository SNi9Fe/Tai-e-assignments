/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral c) {
            return Value.makeConstant(c.getValue());
        } else if (exp instanceof Var v) {
            return in.get(v);
        } else if (exp instanceof BinaryExp be) {
            Value y = in.get(be.getOperand1());
            Value z = in.get(be.getOperand2());
            if (y.isNAC() || z.isNAC()) {
                return Value.getNAC();
            } else if (y.isConstant() && z.isConstant()) {
                int yVal = y.getConstant();
                int zVal = z.getConstant();
                switch (be.getOperator().toString()) {
                    case "+":
                        return Value.makeConstant(yVal + zVal);
                    case "-":
                        return Value.makeConstant(yVal - zVal);
                    case "*":
                        return Value.makeConstant(yVal * zVal);
                    case "/":
                        return Value.makeConstant(yVal / zVal);
                    case "%":
                        return Value.makeConstant(yVal % zVal);
                    case "==":
                        return Value.makeConstant(yVal == zVal ? 1 : 0);
                    case "!=":
                        return Value.makeConstant(yVal != zVal ? 1 : 0);
                    case "<":
                        return Value.makeConstant(yVal < zVal ? 1 : 0);
                    case ">":
                        return Value.makeConstant(yVal > zVal ? 1 : 0);
                    case "<=":
                        return Value.makeConstant(yVal <= zVal ? 1 : 0);
                    case ">=":
                        return Value.makeConstant(yVal >= zVal ? 1 : 0);
                    case "<<":
                        return Value.makeConstant(yVal << zVal);
                    case ">>":
                        return Value.makeConstant(yVal >> zVal);
                    case ">>>":
                        return Value.makeConstant(yVal >>> zVal);
                    case "|":
                        return Value.makeConstant(yVal | zVal);
                    case "&":
                        return Value.makeConstant(yVal & zVal);
                    case "^":
                        return Value.makeConstant(yVal ^ zVal);
                }
            } else {
                return Value.getUndef();
            }
        } else {
            return Value.getNAC();
        }
        return null;
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact cpf = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            if (canHoldInt(param)) {
                cpf.update(param, Value.getNAC());
            }
        }
        return cpf;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.entries().forEach(entry -> {
            target.update(entry.getKey(), meetValue(entry.getValue(), target.get(entry.getKey())));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef() && v2.isConstant()) {
            return v2;
        } else if (v2.isUndef() && v1.isConstant()) {
            return v1;
        } else if (v2.isUndef() && v1.isUndef()) {
            return Value.getUndef();
        } else if (v1.isConstant() && v2.isConstant()) {
            if(v1.getConstant() == v2.getConstant()){
                return v1;
            }else{
                return Value.getNAC();
            }
        }
        return Value.getUndef();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof DefinitionStmt dStmt) {
            CPFact oldOut = out.copy();
            out.copyFrom(in);
            if (dStmt.getLValue() instanceof Var lVal && canHoldInt(lVal)) {
                out.update(lVal, evaluate(dStmt.getRValue(), in));
            }
            return !out.equals(oldOut);
        } else {
            return out.copyFrom(in);
        }
    }
}
