package main;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.FilenameUtils;
import org.metaborg.sdf2table.grammar.ConstructorAttribute;
import org.metaborg.sdf2table.grammar.IAttribute;
import org.metaborg.sdf2table.parsetable.ContextualProduction;
import org.metaborg.sdf2table.parsetable.ParseTableGenerator;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.spoofax.interpreter.terms.IStrategoAppl;
import org.spoofax.interpreter.terms.IStrategoString;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.spoofax.interpreter.terms.ITermFactory;
import org.spoofax.jsglr.client.InvalidParseTableException;
import org.spoofax.jsglr.client.MultiBadTokenException;
import org.spoofax.jsglr.client.ParseTable;
import org.spoofax.jsglr.client.SGLRParseResult;
import org.spoofax.jsglr.client.imploder.TermTreeFactory;
import org.spoofax.jsglr.client.imploder.TreeBuilder;
import org.spoofax.jsglr.io.SGLR;
import org.spoofax.terms.TermFactory;
import org.spoofax.terms.attachments.ParentTermFactory;
import org.strategoxt.lang.Context;
import org.strategoxt.stratego_aterm.aterm_escape_strings_0_0;
import org.strategoxt.stratego_aterm.pp_aterm_box_0_0;
import org.strategoxt.stratego_gpp.box2text_string_0_1;

import com.google.common.base.Charsets;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

public class Main {

    private final static ITermFactory tf = new TermFactory();
    private static Logger debugLogger = LoggerFactory.getLogger(Main.class);
    private static org.apache.log4j.Logger resultLogger = org.apache.log4j.Logger.getLogger("reportsLogger");
    private static org.apache.log4j.Logger JAVAresultLogger = org.apache.log4j.Logger.getLogger("JAVAreportsLogger");
    private final static boolean JAVA = false;
    private final static boolean OCAML = true;
    private final static boolean TESTING = true;
    private final static String testingFile = "test_transaction.ml";
    private final static String testingJavaFile = "disamb.java";

    public static void main(String[] args) {



        File previousFiles = new File("logs/ocaml-files.log");
        if(previousFiles.exists() && previousFiles.length() != 0) {
            try {
                if(JAVA) {
                    resumeJavaExperiment();
                }
                if(OCAML) {
                    resumeOCamlExperiment(previousFiles);
                }
            } catch(Exception e) {
                debugLogger.error("OCaml experiment failed with exception\n{}", e.getMessage());
                if(e instanceof MultiBadTokenException) {
                    MultiBadTokenException mbe = (MultiBadTokenException) e;
                    debugLogger.error("parsing failed at line {}", mbe.getLineNumber());
                }
            }
        } else {

            // tests for Java
            try {
                if(JAVA) {
                    runJavaExperiment();
                }
            } catch(Exception e) {
                debugLogger.error("OCaml experiment failed with exception\n{}", e.getMessage());
                if(e instanceof MultiBadTokenException) {
                    MultiBadTokenException mbe = (MultiBadTokenException) e;
                    debugLogger.error("parsing failed at line {}", mbe.getLineNumber());
                }
            }

            // tests for OCaml
            try {
                if(OCAML) {
                    runOCamlExperiment();
                }
            } catch(Exception e) {
                debugLogger.error("OCaml experiment failed with exception\n{}", e.getMessage());
                if(e instanceof MultiBadTokenException) {
                    MultiBadTokenException mbe = (MultiBadTokenException) e;
                    debugLogger.error("parsing failed at line {}", mbe.getLineNumber());
                }
            }
        }

    }

    private static void runJavaExperiment() {
        // Go through all Java files:
        // count LOC
        // parse them
        // count AST nodes
        // parse them using a new dynamic parse table and the same parse table as the other programs
        // parse them disabling contextual productions and count ambiguities
        // TODO set up how to count disambiguation by brackets
        org.apache.log4j.Logger filesLogger = org.apache.log4j.Logger.getLogger("JAVAfilesLogger");
        org.apache.log4j.Logger probfilesLogger = org.apache.log4j.Logger.getLogger("JAVAproblematicfilesLogger");


        int filesParsed = 0;

        debugLogger.info("-------------------------------------");
        debugLogger.info("Creating the list of all Java Files:");
        File oCamlDir = new File("test/Java/");
        Collection<File> javaFiles = FileUtils.listFiles(oCamlDir, new String[] { "java" }, true);
        debugLogger.info("{} files created.", javaFiles.size());
        debugLogger.info("-------------------------------------");

        final TermTreeFactory factory = new TermTreeFactory(new ParentTermFactory(tf));
        File mainOcamlFile = new File("normalizedGrammars/Java/normalized/java-front-norm.aterm");
        ParseTableGenerator ptg = new ParseTableGenerator(mainOcamlFile, null, null, null,
            Lists.newArrayList("normalizedGrammars/Java"), false);

        IStrategoTerm ptAterm, noOperatorAmbPTAterm, noDanglingElsePTAterm, noLongestMatchPTAterm;
        ParseTableGenerator noOperatorAmbPtg, noDanglingElsePtg, noLongestMatchPtg;
        SGLR parserAllFiles, noOperatorAmbParser, noDanglingElseParser, noLongestMatchParser;
        ParseTable pt, noOperatorAmbPT, noDanglingElsePT, noLongestMatchPT;

        try {
            ptAterm = ptg.createDynamicTable(true, true, true, true);

            noOperatorAmbPtg = new ParseTableGenerator(mainOcamlFile, null, null, null,
                Lists.newArrayList("normalizedGrammars/Java"), false);
            noOperatorAmbPTAterm = noOperatorAmbPtg.createDynamicTable(false, true, true, true);

            noDanglingElsePtg = new ParseTableGenerator(mainOcamlFile, null, null, null,
                Lists.newArrayList("normalizedGrammars/Java"), false);
            noDanglingElsePTAterm = noDanglingElsePtg.createDynamicTable(true, false, true, true);

            noLongestMatchPtg = new ParseTableGenerator(mainOcamlFile, null, null, null,
                Lists.newArrayList("normalizedGrammars/Java"), false);
            noLongestMatchPTAterm = noLongestMatchPtg.createDynamicTable(true, true, false, true);

            pt = new ParseTable(ptAterm, tf, ptg.getGrammar());
            noOperatorAmbPT = new ParseTable(noOperatorAmbPTAterm, tf, noOperatorAmbPtg.getGrammar());
            noDanglingElsePT = new ParseTable(noDanglingElsePTAterm, tf, noDanglingElsePtg.getGrammar());
            noLongestMatchPT = new ParseTable(noLongestMatchPTAterm, tf, noLongestMatchPtg.getGrammar());


            parserAllFiles = new SGLR(new TreeBuilder(factory), pt);
            noOperatorAmbParser = new SGLR(new TreeBuilder(factory), noOperatorAmbPT);
            noDanglingElseParser = new SGLR(new TreeBuilder(factory), noDanglingElsePT);
            noLongestMatchParser = new SGLR(new TreeBuilder(factory), noLongestMatchPT);

            setParser(parserAllFiles);

        } catch(Exception e) {
            debugLogger.info("Failed to create the parse table");
            return;
        }

        int i = 0;

        for(File f : javaFiles) {
            // if testing, only use disamb.ml, if not, skip disamb.ml
            if(TESTING) {
                if(!f.getName().equals(testingJavaFile)) {
                    continue;
                }
            } else {
                if(f.getName().equals(testingJavaFile)) {
                    continue;
                }
            }

            // FIXME the files below cause a stack overflow when imploding
            if(checkProblematicFiles(f)) {
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            if(i != 0) {
                debugLogger.info("");
                JAVAresultLogger.info("\n");
            }
            i++;

            debugLogger.info(f.getAbsolutePath());
            JAVAresultLogger.info(f.getName() + ";");

            long lineCount;
            String input;
            try {
                input = FileUtils.readFileToString(f, Charsets.UTF_8);
                lineCount = getLineCount(f);
            } catch(IOException e) {
                debugLogger.info("Could not open file.");
                JAVAresultLogger.info("could not open file");
                e.printStackTrace();
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            debugLogger.info("{} lines.", lineCount);
            JAVAresultLogger.info(lineCount + ";");

            ParseTable individualPT;
            try {
                individualPT = new ParseTable(ptAterm, tf, ptg.getGrammar());
            } catch(InvalidParseTableException e) {
                debugLogger.info("Could not create individual parse table.");
                JAVAresultLogger.info("could not create individual parse table;");
                e.printStackTrace();
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            SGLR individualParser = new SGLR(new TreeBuilder(factory), individualPT);


            SGLRParseResult parseResult;
            try {
                parseResult = parserAllFiles.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Parsing failed with exception {}", e.getMessage());
                JAVAresultLogger.info("parsing failed.");
                e.printStackTrace();
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            SGLRParseResult individualParseResult;
            try {
                individualParseResult = individualParser.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Parsing failed with exception {}", e.getMessage());
                JAVAresultLogger.info("parsing failed.");
                e.printStackTrace();
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            SGLRParseResult noOperatorAmbResult;
            try {
                noOperatorAmbResult = noOperatorAmbParser.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Operator-style ambiguity parser failed with exception {}", e.getMessage());
                JAVAresultLogger.info("operator-style parsing failed.");
                e.printStackTrace();
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            SGLRParseResult noDanglingElseResult;
            try {
                noDanglingElseResult = noDanglingElseParser.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Dangling else parser failed with exception {}", e.getMessage());
                JAVAresultLogger.info("dangling else parsing failed.");
                e.printStackTrace();
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            SGLRParseResult noLongestMatchResult;
            try {
                noLongestMatchResult = noLongestMatchParser.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Longest match parser failed with exception {}", e.getMessage());
                JAVAresultLogger.info("longest match parsing failed.");
                e.printStackTrace();
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            IStrategoTerm ast = (IStrategoTerm) parseResult.output;
            IStrategoTerm individualAst = (IStrategoTerm) individualParseResult.output;
            IStrategoTerm noOperatorAmbAst = (IStrategoTerm) noOperatorAmbResult.output;
            IStrategoTerm noDanglingElseAst = (IStrategoTerm) noDanglingElseResult.output;
            IStrategoTerm noLongestMatchAst = (IStrategoTerm) noLongestMatchResult.output;

            if(!ast.equals(individualAst)) {
                debugLogger.info("AST from local parser is different from AST from global parser.");
                JAVAresultLogger.info("local and global asts are different;");
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            long ambs = parserAllFiles.getAmbiguitiesCount();
            long opStyleAmbs = noOperatorAmbParser.getAmbiguitiesCount();
            long danglingElseAmbs = noDanglingElseParser.getAmbiguitiesCount();
            long longestMatchAmbs = noLongestMatchParser.getAmbiguitiesCount();

            if(ambs != 0) {
                debugLogger.info("Original input contains ambiguities");
                JAVAresultLogger.info("input contains ambiguities;");
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            if(opStyleAmbs != 0) {
                exportAmbiguities(f, noOperatorAmbAst, "operator-style");
            }

            if(danglingElseAmbs != 0) {
                exportAmbiguities(f, noDanglingElseAst, "dangling-else");
            }

            if(longestMatchAmbs != 0) {
                exportAmbiguities(f, noLongestMatchAst, "longest-match");
            }

            long nodeCount = getNodeCount(ast);
            long totalStates = individualPT.getPTgenerator().totalStates();
            long processedStates = individualPT.getPTgenerator().getProcessedStates();
            debugLogger.info("{} ast nodes.", nodeCount);
            debugLogger.info("Visited {} states.", totalStates);
            debugLogger.info("And processed {} states.", processedStates);

            JAVAresultLogger.info(nodeCount + ";");
            JAVAresultLogger.info(totalStates + ";");
            JAVAresultLogger.info(processedStates + ";");

            debugLogger.info("{} ambiguities.", ambs);
            debugLogger.info("{} operator-style ambiguities.", opStyleAmbs);
            debugLogger.info("{} dangling else ambiguities.", danglingElseAmbs);
            debugLogger.info("{} longest match ambiguities.", longestMatchAmbs);

            JAVAresultLogger.info(opStyleAmbs + ";");
            JAVAresultLogger.info(danglingElseAmbs + ";");
            JAVAresultLogger.info(longestMatchAmbs + ";");

            filesLogger.info(f.getAbsolutePath());
            filesParsed++;
        }

        long finalStates = pt.getPTgenerator().totalStates();
        long finalProcessedStates = pt.getPTgenerator().getProcessedStates();

        debugLogger.info("");
        debugLogger.info("-------------------------------------");
        debugLogger.info("All programs visited {} states.", finalStates);
        debugLogger.info("and processed {} states.", finalProcessedStates);
        debugLogger.info("Files parsed: {}", filesParsed);
        debugLogger.info("Files that did not parse: {}", javaFiles.size() - filesParsed);
        debugLogger.info("-------------------------------------");

        JAVAresultLogger.info("\n\n\n" + finalStates + ";" + finalProcessedStates);
    }

    private static void resumeJavaExperiment() {
        // TODO implement java experiment

    }

    private static void runOCamlExperiment() {
        // Go through all OCaml files:
        // count LOC
        // parse them
        // count AST nodes
        // parse them using a new dynamic parse table and the same parse table as the other programs
        // parse them disabling contextual productions and count ambiguities
        // TODO set up how to count disambiguation by brackets
        org.apache.log4j.Logger filesLogger = org.apache.log4j.Logger.getLogger("filesLogger");
        org.apache.log4j.Logger probfilesLogger = org.apache.log4j.Logger.getLogger("problematicfilesLogger");

        int filesParsed = 0;

        debugLogger.info("-------------------------------------");
        debugLogger.info("Creating the list of all OCaml Files:");
        File oCamlDir = new File("test/OCaml/");
        Collection<File> oCamlFiles = FileUtils.listFiles(oCamlDir, new String[] { "ml" }, true);
        debugLogger.info("{} files created.", oCamlFiles.size());
        debugLogger.info("-------------------------------------");

        final TermTreeFactory factory = new TermTreeFactory(new ParentTermFactory(tf));
        File mainOcamlFile = new File("normalizedGrammars/OCaml/normalized/OCaml-norm.aterm");
        ParseTableGenerator ptg = new ParseTableGenerator(mainOcamlFile, null, null, null,
            Lists.newArrayList("normalizedGrammars/OCaml"), false);

        IStrategoTerm ptAterm, noOperatorAmbPTAterm, noDanglingElsePTAterm, noLongestMatchPTAterm;
        ParseTableGenerator noOperatorAmbPtg, noDanglingElsePtg, noLongestMatchPtg;
        SGLR parserAllFiles, noOperatorAmbParser, noDanglingElseParser, noLongestMatchParser;
        ParseTable pt, noOperatorAmbPT, noDanglingElsePT, noLongestMatchPT;

        try {
            ptAterm = ptg.createDynamicTable(true, true, true, true);

            noOperatorAmbPtg = new ParseTableGenerator(mainOcamlFile, null, null, null,
                Lists.newArrayList("normalizedGrammars/OCaml"), false);
            noOperatorAmbPTAterm = noOperatorAmbPtg.createDynamicTable(false, true, true, true);

            noDanglingElsePtg = new ParseTableGenerator(mainOcamlFile, null, null, null,
                Lists.newArrayList("normalizedGrammars/OCaml"), false);
            noDanglingElsePTAterm = noDanglingElsePtg.createDynamicTable(true, false, true, true);

            noLongestMatchPtg = new ParseTableGenerator(mainOcamlFile, null, null, null,
                Lists.newArrayList("normalizedGrammars/OCaml"), false);
            noLongestMatchPTAterm = noLongestMatchPtg.createDynamicTable(true, true, false, true);

            pt = new ParseTable(ptAterm, tf, ptg.getGrammar());
            noOperatorAmbPT = new ParseTable(noOperatorAmbPTAterm, tf, noOperatorAmbPtg.getGrammar());
            noDanglingElsePT = new ParseTable(noDanglingElsePTAterm, tf, noDanglingElsePtg.getGrammar());
            noLongestMatchPT = new ParseTable(noLongestMatchPTAterm, tf, noLongestMatchPtg.getGrammar());


            parserAllFiles = new SGLR(new TreeBuilder(factory), pt);
            noOperatorAmbParser = new SGLR(new TreeBuilder(factory), noOperatorAmbPT);
            noDanglingElseParser = new SGLR(new TreeBuilder(factory), noDanglingElsePT);
            noLongestMatchParser = new SGLR(new TreeBuilder(factory), noLongestMatchPT);

            setParser(parserAllFiles);

        } catch(Exception e) {
            debugLogger.info("Failed to create the parse table");
            return;
        }

        int i = 0;

        for(File f : oCamlFiles) {
            // if testing, only use disamb.ml, if not, skip disamb.ml
            if(TESTING) {
                if(!f.getName().equals(testingFile)) {
                    continue;
                }
            } else {
                if(f.getName().equals(testingFile)) {
                    continue;
                }
            }

            // FIXME the files below cause a stack overflow when imploding
            if(checkProblematicFiles(f)) {
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            if(i != 0) {
                debugLogger.info("");
                resultLogger.info("\n");
            }
            i++;

            debugLogger.info(f.getAbsolutePath());
            resultLogger.info(f.getName() + ";");

            long lineCount;
            String input;
            try {
                input = FileUtils.readFileToString(f, Charsets.UTF_8);
                lineCount = getLineCount(f);
            } catch(IOException e) {
                debugLogger.info("Could not open file.");
                resultLogger.info("could not open file");
                e.printStackTrace();
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            debugLogger.info("{} lines.", lineCount);
            resultLogger.info(lineCount + ";");

            ParseTable individualPT;
            try {
                individualPT = new ParseTable(ptAterm, tf, ptg.getGrammar());
            } catch(InvalidParseTableException e) {
                debugLogger.info("Could not create individual parse table.");
                resultLogger.info("could not create individual parse table;");
                e.printStackTrace();
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            SGLR individualParser = new SGLR(new TreeBuilder(factory), individualPT);


            SGLRParseResult parseResult;
            try {
                parseResult = parserAllFiles.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Parsing failed with exception {}", e.getMessage());
                resultLogger.info("parsing failed.");
                e.printStackTrace();
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            SGLRParseResult individualParseResult;
            try {
                individualParseResult = individualParser.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Parsing failed with exception {}", e.getMessage());
                resultLogger.info("parsing failed.");
                e.printStackTrace();
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            SGLRParseResult noOperatorAmbResult;
            try {
                noOperatorAmbResult = noOperatorAmbParser.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Operator-style ambiguity parser failed with exception {}", e.getMessage());
                resultLogger.info("operator-style parsing failed.");
                e.printStackTrace();
                continue;
            }

            SGLRParseResult noDanglingElseResult;
            try {
                noDanglingElseResult = noDanglingElseParser.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Dangling else parser failed with exception {}", e.getMessage());
                resultLogger.info("dangling else parsing failed.");
                e.printStackTrace();
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            SGLRParseResult noLongestMatchResult;
            try {
                noLongestMatchResult = noLongestMatchParser.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Longest match parser failed with exception {}", e.getMessage());
                resultLogger.info("longest match parsing failed.");
                e.printStackTrace();
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            IStrategoTerm ast = (IStrategoTerm) parseResult.output;
            IStrategoTerm individualAst = (IStrategoTerm) individualParseResult.output;
            IStrategoTerm noOperatorAmbAst = (IStrategoTerm) noOperatorAmbResult.output;
            IStrategoTerm noDanglingElseAst = (IStrategoTerm) noDanglingElseResult.output;
            IStrategoTerm noLongestMatchAst = (IStrategoTerm) noLongestMatchResult.output;

            if(!ast.equals(individualAst)) {
                debugLogger.info("AST from local parser is different from AST from global parser.");
                resultLogger.info("local and global asts are different;");
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            long ambs = parserAllFiles.getAmbiguitiesCount();
            long opStyleAmbs = noOperatorAmbParser.getAmbiguitiesCount();
            long danglingElseAmbs = noDanglingElseParser.getAmbiguitiesCount();
            long longestMatchAmbs = noLongestMatchParser.getAmbiguitiesCount();

            if(ambs != 0) {
                debugLogger.info("Original input contains ambiguities");
                resultLogger.info("input contains ambiguities;");
                probfilesLogger.info(f.getAbsolutePath());
                continue;
            }

            if(opStyleAmbs != 0) {
                exportAmbiguities(f, noOperatorAmbAst, "operator-style");
            }

            if(danglingElseAmbs != 0) {
                exportAmbiguities(f, noDanglingElseAst, "dangling-else");
            }

            if(longestMatchAmbs != 0) {
                exportAmbiguities(f, noLongestMatchAst, "longest-match");
            }

            long nodeCount = getNodeCount(ast);
            long disambiguatingBrackets = getDisambiguatingBrackets(ast, ptg);
            long totalStates = individualPT.getPTgenerator().totalStates();
            long processedStates = individualPT.getPTgenerator().getProcessedStates();
            debugLogger.info("{} ast nodes.", nodeCount);
            debugLogger.info("Visited {} states.", totalStates);
            debugLogger.info("And processed {} states.", processedStates);

            resultLogger.info(nodeCount + ";");
            resultLogger.info(totalStates + ";");
            resultLogger.info(processedStates + ";");

            debugLogger.info("{} ambiguities.", ambs);
            debugLogger.info("{} operator-style ambiguities.", opStyleAmbs);
            debugLogger.info("{} dangling else ambiguities.", danglingElseAmbs);
            debugLogger.info("{} longest match ambiguities.", longestMatchAmbs);

            resultLogger.info(opStyleAmbs + ";");
            resultLogger.info(danglingElseAmbs + ";");
            resultLogger.info(longestMatchAmbs + ";");

            filesLogger.info(f.getAbsolutePath());
            filesParsed++;
        }

        long finalStates = pt.getPTgenerator().totalStates();
        long finalProcessedStates = pt.getPTgenerator().getProcessedStates();

        debugLogger.info("");
        debugLogger.info("-------------------------------------");
        debugLogger.info("All programs visited {} states.", finalStates);
        debugLogger.info("and processed {} states.", finalProcessedStates);
        debugLogger.info("Files parsed: {}", filesParsed);
        debugLogger.info("Files that did not parse: {}", oCamlFiles.size() - filesParsed);
        debugLogger.info("-------------------------------------");

        resultLogger.info("\n\n\n" + finalStates + ";" + finalProcessedStates);
    }

    private static long getDisambiguatingBrackets(IStrategoTerm ast, ParseTableGenerator ptg) {
        List<ContextualProduction> conflictingProductions = Lists.newArrayList(ptg.getGrammar().contextual_prods.values());
        Map<ContextualProduction, ConstructorAttribute> prod_cons = Maps.newHashMap();
        
        for(ContextualProduction p : conflictingProductions) {
            for(IAttribute attr : ptg.getGrammar().prod_attrs.get(p.getOrigProduction())){
                if(attr instanceof ConstructorAttribute) {
                    prod_cons.put(p, (ConstructorAttribute) attr);
                }
            }
        }
        
        System.out.println("");
        
        return 0;
    }

    private static void resumeOCamlExperiment(File previousFiles) {
        String processedFiles;
        try {
            processedFiles = FileUtils.readFileToString(previousFiles, Charsets.UTF_8);
        } catch(IOException e) {
            debugLogger.info("Could not open file containing files processed previously.");
            resultLogger.info("could not open file containing files processed previously");
            e.printStackTrace();
            return;
        }

        org.apache.log4j.Logger filesLogger = org.apache.log4j.Logger.getLogger("filesLogger");

        File oCamlDir = new File("test/OCaml/");
        Collection<File> oCamlFiles = FileUtils.listFiles(oCamlDir, new String[] { "ml" }, true);

        final TermTreeFactory factory = new TermTreeFactory(new ParentTermFactory(tf));
        File mainOcamlFile = new File("normalizedGrammars/OCaml/normalized/OCaml-norm.aterm");
        ParseTableGenerator ptg = new ParseTableGenerator(mainOcamlFile, null, null, null,
            Lists.newArrayList("normalizedGrammars/OCaml"), false);

        IStrategoTerm ptAterm, noOperatorAmbPTAterm, noDanglingElsePTAterm, noLongestMatchPTAterm;
        ParseTableGenerator noOperatorAmbPtg, noDanglingElsePtg, noLongestMatchPtg;
        SGLR parserAllFiles, noOperatorAmbParser, noDanglingElseParser, noLongestMatchParser;
        ParseTable pt, noOperatorAmbPT, noDanglingElsePT, noLongestMatchPT;

        try {
            ptAterm = ptg.createDynamicTable(true, true, true, true);

            noOperatorAmbPtg = new ParseTableGenerator(mainOcamlFile, null, null, null,
                Lists.newArrayList("normalizedGrammars/OCaml"), false);
            noOperatorAmbPTAterm = noOperatorAmbPtg.createDynamicTable(false, true, true, true);

            noDanglingElsePtg = new ParseTableGenerator(mainOcamlFile, null, null, null,
                Lists.newArrayList("normalizedGrammars/OCaml"), false);
            noDanglingElsePTAterm = noDanglingElsePtg.createDynamicTable(true, false, true, true);

            noLongestMatchPtg = new ParseTableGenerator(mainOcamlFile, null, null, null,
                Lists.newArrayList("normalizedGrammars/OCaml"), false);
            noLongestMatchPTAterm = noLongestMatchPtg.createDynamicTable(true, true, false, true);

            pt = new ParseTable(ptAterm, tf, ptg.getGrammar());
            noOperatorAmbPT = new ParseTable(noOperatorAmbPTAterm, tf, noOperatorAmbPtg.getGrammar());
            noDanglingElsePT = new ParseTable(noDanglingElsePTAterm, tf, noDanglingElsePtg.getGrammar());
            noLongestMatchPT = new ParseTable(noLongestMatchPTAterm, tf, noLongestMatchPtg.getGrammar());


            parserAllFiles = new SGLR(new TreeBuilder(factory), pt);
            noOperatorAmbParser = new SGLR(new TreeBuilder(factory), noOperatorAmbPT);
            noDanglingElseParser = new SGLR(new TreeBuilder(factory), noDanglingElsePT);
            noLongestMatchParser = new SGLR(new TreeBuilder(factory), noLongestMatchPT);

            setParser(parserAllFiles);

        } catch(Exception e) {
            debugLogger.info("Failed to create the parse table");
            return;
        }

        int i = 0;

        for(File f : oCamlFiles) {
            // if testing, only use disamb.ml, if not, skip disamb.ml
            if(TESTING) {
                if(!f.getName().equals(testingFile)) {
                    continue;
                }
            } else {
                if(f.getName().equals(testingFile)) {
                    continue;
                }
            }

            if(processedFiles.contains(f.getAbsolutePath())) {
                continue;
            }

            // FIXME the files below cause a stack overflow when imploding or makes the parser hang
            if(checkProblematicFiles(f)) {
                continue;
            }

            if(i != 0) {
                debugLogger.info("");
                resultLogger.info("\n");
            }
            i++;

            debugLogger.info(f.getAbsolutePath());
            resultLogger.info(f.getName() + ";");

            long lineCount;
            String input;
            try {
                input = FileUtils.readFileToString(f, Charsets.UTF_8);
                lineCount = getLineCount(f);
            } catch(IOException e) {
                debugLogger.info("Could not open file.");
                resultLogger.info("could not open file");
                e.printStackTrace();
                continue;
            }

            debugLogger.info("{} lines.", lineCount);
            resultLogger.info(lineCount + ";");

            ParseTable individualPT;
            try {
                individualPT = new ParseTable(ptAterm, tf, ptg.getGrammar());
            } catch(InvalidParseTableException e) {
                debugLogger.info("Could not create individual parse table.");
                resultLogger.info("could not create individual parse table;");
                e.printStackTrace();
                continue;
            }

            SGLR individualParser = new SGLR(new TreeBuilder(factory), individualPT);


            SGLRParseResult parseResult;
            try {
                parseResult = parserAllFiles.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Parsing failed with exception {}", e.getMessage());
                resultLogger.info("parsing failed.");
                e.printStackTrace();
                continue;
            }

            SGLRParseResult individualParseResult;
            try {
                individualParseResult = individualParser.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Parsing failed with exception {}", e.getMessage());
                resultLogger.info("parsing failed.");
                e.printStackTrace();
                continue;
            }

            SGLRParseResult noOperatorAmbResult;
            try {
                noOperatorAmbResult = noOperatorAmbParser.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Operator-style ambiguity parser failed with exception {}", e.getMessage());
                resultLogger.info("operator-style parsing failed.");
                e.printStackTrace();
                continue;
            }

            SGLRParseResult noDanglingElseResult;
            try {
                noDanglingElseResult = noDanglingElseParser.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Dangling else parser failed with exception {}", e.getMessage());
                resultLogger.info("dangling else parsing failed.");
                e.printStackTrace();
                continue;
            }

            SGLRParseResult noLongestMatchResult;
            try {
                noLongestMatchResult = noLongestMatchParser.parse(input, f.getName(), "Start");
            } catch(Exception e) {
                debugLogger.info("Longest match parser failed with exception {}", e.getMessage());
                resultLogger.info("longest match parsing failed.");
                e.printStackTrace();
                continue;
            }

            IStrategoTerm ast = (IStrategoTerm) parseResult.output;
            IStrategoTerm individualAst = (IStrategoTerm) individualParseResult.output;
            IStrategoTerm noOperatorAmbAst = (IStrategoTerm) noOperatorAmbResult.output;
            IStrategoTerm noDanglingElseAst = (IStrategoTerm) noDanglingElseResult.output;
            IStrategoTerm noLongestMatchAst = (IStrategoTerm) noLongestMatchResult.output;

            if(!ast.equals(individualAst)) {
                debugLogger.info("AST from local parser is different from AST from global parser.");
                resultLogger.info("local and global asts are different;");
                continue;
            }

            long ambs = parserAllFiles.getAmbiguitiesCount();
            long opStyleAmbs = noOperatorAmbParser.getAmbiguitiesCount();
            long danglingElseAmbs = noDanglingElseParser.getAmbiguitiesCount();
            long longestMatchAmbs = noLongestMatchParser.getAmbiguitiesCount();

            if(ambs != 0) {
                debugLogger.info("Original input contains ambiguities");
                resultLogger.info("input contains ambiguities;");
                continue;
            }

            if(opStyleAmbs != 0) {
                exportAmbiguities(f, noOperatorAmbAst, "operator-style");
            }

            if(danglingElseAmbs != 0) {
                exportAmbiguities(f, noDanglingElseAst, "dangling-else");
            }

            if(longestMatchAmbs != 0) {
                exportAmbiguities(f, noLongestMatchAst, "longest-match");
            }

            long nodeCount = getNodeCount(ast);
            long totalStates = individualPT.getPTgenerator().totalStates();
            long processedStates = individualPT.getPTgenerator().getProcessedStates();
            debugLogger.info("{} ast nodes.", nodeCount);
            debugLogger.info("Visited {} states.", totalStates);
            debugLogger.info("And processed {} states.", processedStates);

            resultLogger.info(nodeCount + ";");
            resultLogger.info(totalStates + ";");
            resultLogger.info(processedStates + ";");

            debugLogger.info("{} ambiguities.", ambs);
            debugLogger.info("{} operator-style ambiguities.", opStyleAmbs);
            debugLogger.info("{} dangling else ambiguities.", danglingElseAmbs);
            debugLogger.info("{} longest match ambiguities.", longestMatchAmbs);

            resultLogger.info(opStyleAmbs + ";");
            resultLogger.info(danglingElseAmbs + ";");
            resultLogger.info(longestMatchAmbs + ";");

            filesLogger.info(f.getAbsolutePath());
        }


        debugLogger.info("");

        debugLogger.info("-----------------------------------------------------------------------------------------");
        debugLogger.warn("PLEASE RE-RUN THE FULL EXPERIMENT TO GET THE CORRECT NUMBER OF FINAL AND PROCESSED STATES");
        debugLogger.info("-----------------------------------------------------------------------------------------");

        resultLogger
            .info("\n\nPLEASE RE-RUN THE FULL EXPERIMENT TO GET THE CORRECT NUMBER OF FINAL AND PROCESSED STATES");

    }

    private static boolean checkProblematicFiles(File f) {
        // too many longest-match ambiguities
        return f.getPath().equals("test/OCaml/bucklescript/jscomp/test/gpr_1150.ml")
            // too many operator-style ambiguities
            || f.getPath().equals("test/OCaml/tezos/src/node/shell/validator.ml")
            || f.getPath().equals("test/OCaml/tezos/src/proto/alpha/amendment.ml")
            || f.getPath().equals("test/OCaml/tezos/test/p2p/test_p2p_connection_pool.ml")
            // too many unicode characters?
            || f.getPath().equals("test/OCaml/bucklescript/jscomp/test/string_interp_test.ml")
            || f.getPath().equals("test/OCaml/bucklescript/jscomp/test/chn_test.ml")
            || f.getPath().equals("test/OCaml/tezos/src/client/client_network.ml");

    }

    private static void exportAmbiguities(File f, IStrategoTerm ast, String kind) {
        // export ambiguities to logs/ambs/{path}/kind/name
        final Path filePath = Paths.get(f.toURI());
        final String projectPath = System.getProperty("user.dir");
        final Path basePath = Paths.get(projectPath, "test");

        final Path relativePath = basePath.relativize(filePath);

        File outputFile = new File("logs/ambiguities/" + relativePath.getParent() + "/" + kind + "/"
            + FilenameUtils.removeExtension(relativePath.getFileName().toString()) + ".aterm");
        File parentDir = outputFile.getParentFile();
        if(!parentDir.exists()) {
            parentDir.mkdirs();
        }

        List<IStrategoTerm> ambs = collectAmbs(ast);

        FileWriter out = null;
        try {
            out = new FileWriter(outputFile);
            // output ambiguity
            int i = 0;
            for(IStrategoTerm amb : ambs) {
                out.write("Ambiguity " + ++i + ": \n");
                out.write(prettyPrint(amb).stringValue());
            }
            out.close();
        } catch(IOException e) {
            System.err.println(e.getMessage());
        }
    }

    private static void setParser(SGLR parser) {
        parser.setCompletionParse(false, Integer.MAX_VALUE);
        parser.setTimeout(30000);
    }

    private static long getNodeCount(IStrategoTerm ast) {
        int nc = 0;
        for(IStrategoTerm child : ast.getAllSubterms()) {
            nc += getNodeCount(child);
        }

        return nc + 1;
    }

    private static List<IStrategoTerm> collectAmbs(IStrategoTerm ast) {
        List<IStrategoTerm> ambs = Lists.newArrayList();

        if(ast instanceof IStrategoAppl) {
            IStrategoAppl amb = (IStrategoAppl) ast;
            if(amb.getConstructor().getName().equals("amb")) {
                ambs.add(ast);
            }
        }

        for(IStrategoTerm child : ast.getAllSubterms()) {
            ambs.addAll(collectAmbs(child));
        }

        return ambs;
    }

    private static IStrategoString prettyPrint(IStrategoTerm term) {
        org.strategoxt.lang.Context context = new Context(tf);
        org.strategoxt.stratego_aterm.Main.init(context);
        term = aterm_escape_strings_0_0.instance.invoke(context, term);
        term = pp_aterm_box_0_0.instance.invoke(context, term);
        term = box2text_string_0_1.instance.invoke(context, term, tf.makeInt(120));
        return (IStrategoString) term;
    }

    /**
     * Count file rows.
     *
     * @param file
     *            file
     * @return file row count
     * @throws IOException
     */
    private static long getLineCount(File file) throws IOException {

        try(BufferedInputStream is = new BufferedInputStream(new FileInputStream(file), 1024)) {

            byte[] c = new byte[1024];
            boolean empty = true, lastEmpty = false;
            long count = 0;
            int read;
            while((read = is.read(c)) != -1) {
                for(int i = 0; i < read; i++) {
                    if(c[i] == '\n') {
                        count++;
                        lastEmpty = true;
                    } else if(lastEmpty) {
                        lastEmpty = false;
                    }
                }
                empty = false;
            }

            if(!empty) {
                if(count == 0) {
                    count = 1;
                } else if(!lastEmpty) {
                    count++;
                }
            }

            return count;
        }
    }


}
