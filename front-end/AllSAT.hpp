#ifndef ALLSAT_HPP_
#define ALLSAT_HPP_

#include <string>
#include <iostream>
#include <vector>
#include <iomanip>
#include <map>
#include <iterator>
#include <boost/filesystem.hpp>
#include <boost/process.hpp>
#include <sqlite3.h>

#define DEBUG

class AllSAT {
public:
	/**
	 * @brief CTOR
	 */
	AllSAT(std::string const & directory){
		p_dir = directory;
		p_execution_depth = 1;
		p_database_path = "database.db";
	}

	/**
	 * @brief DTOR
	 */
	~AllSAT(){
		// Chill dude - there are no memory leaks 8)
	}

	/**
	 * brief Initialize AllSAT: Read the file
	 */
	void init(){
		try{
			this->read_directory();
			this->read_files();
		} catch (...){
				std::cerr << "Unrecognized error happened..." << std::endl;
		}
	}

	/**
	 * @brief List all files in the dir
	 *
	 * @param stream The ostream to dump the stream to
	 */
	void list_files (std::ostream & stream = std::cout){
		std::vector<std::string>::const_iterator itor;
		std::string header = "files found";
		size_t max_file_len = 0;
		size_t const left_right_gap = 5;
		for(itor = p_files.begin(); itor != p_files.end(); ++itor){
			if(itor->size() > max_file_len){
				max_file_len = itor->size();
			}
		}

		if(header.size() > max_file_len){
			max_file_len = header.size();
		}

		stream << std::string(left_right_gap + max_file_len + left_right_gap, '#') << std::endl;
		stream << std::left << std::string(left_right_gap, '#')
			   << " " << std::setw((2*left_right_gap + max_file_len)-header.size()-1) << header << " "
			   << std::right << std::string((left_right_gap), '#') << std::endl;
		stream << std::string(left_right_gap + max_file_len + left_right_gap, '#') << std::endl;

		for(itor = p_files.begin(); itor != p_files.end(); ++itor){
			stream << *itor << std::endl;
		}
		stream << std::string(left_right_gap + max_file_len + left_right_gap, '#') << std::endl;
	}

	/**
	 * @brief Dump structured file content to ostream
	 *
	 * @param stream The ostream to pipe the output to
	 */
	void dump_files(std::ostream & stream = std::cout){
		for(std::vector<FileStructure>::iterator itor = p_filestructures.begin(); itor != p_filestructures.end(); ++itor){
			itor->dump(stream);
		}
	}

	/**
	 * @brief Execute AllSAT on ALL found files in the directory
	 */
	void run (){
		for(std::vector<FileStructure>::iterator itor = p_filestructures.begin(); itor != p_filestructures.end(); ++itor){
			this->execute_allsat(*itor);
		}
	}

	/**
	 * @brief Set the maxmimum number of solutions to be found
	 *
	 * @param solutions The maximum solutions
	 */
	void setMaximalSolutions(size_t const solutions){
		p_execution_depth = solutions;
	}

	/**
	 * @brief Get the currently defined number used as maximum for found solutions
	 *
	 * @return The currently active depth
	 */
	size_t getMaximalSolutions() const {
		return p_execution_depth;
	}

	/**
	 * @brief Print the results of AllSAT
	 *
	 * @param stream The stream to pipe the results to
	 */
	void get_results_from_database(std::ostream & stream = std::cout){
		try{
			sqlite3 * db;
			if(sqlite3_open(p_database_path.c_str(), &db) != 0){
				std::string error_msg = "Could now open database: " + p_database_path;
					throw std::runtime_error(error_msg);
			}

			char * error_msg = 0;
			std::string query = "SELECT * FROM allsat;";
			if(sqlite3_exec(db, query.c_str(), c_callback, this, &error_msg) != 0){
				std::string error_msg = "Can not execute query: " + query;
				throw std::runtime_error(error_msg);
			}
			sqlite3_close(db);

			// find max len of each col
			size_t max_reg = 0;
			size_t max_val = 0;
			size_t max_sol = 0;
			size_t max_path = 0;
			for(std::vector<SingleResultPair>::const_iterator itor = p_from_db.begin(); itor != p_from_db.end(); ++itor){
				if (itor->reg_name.size () > max_reg){
					max_reg = itor->reg_name.size();
				}
				if(itor->reg_val.size() > max_val){
					max_val = itor->reg_val.size();
				}
				std::string tmp = std::to_string(itor->solution);
				if (tmp.size() > max_sol){
					max_sol = tmp.size();
				}
				if (itor->path.size() > max_path){
					max_path = itor-> path.size();
				}
			}

			std::string head_name = "register_name";
			std::string head_val = "register_val";
			std::string head_sol = "solutions";
			std::string head_path = "found_path";

			if (head_name.size() > max_reg){
				max_reg = head_name.size();
			}
			if(head_val.size() > max_val){
				max_val = head_val.size();
			}
			if (head_sol.size() > max_sol){
				max_sol = head_sol.size();
			}
			if (head_path.size() > max_path){
				max_path = head_path.size();
			}


			stream << std::left << std::setw(max_reg)  << head_name << " ";
			stream << std::left << std::setw(max_val)  << head_val  << " ";
			stream << std::left << std::setw(max_sol)  << head_sol  << " ";
			stream << std::left << std::setw(max_path) << head_path << std::endl;

			stream << std::left << std::setw(max_reg)  << std::string(max_reg,'-') << " ";
			stream << std::left << std::setw(max_val)  << std::string(max_val, '-') << " ";
			stream << std::left << std::setw(max_sol)  << std::string(max_sol, '-') << " ";
			stream << std::left << std::setw(max_path) << std::string(max_path, '-') << std::endl;

			for(std::vector<SingleResultPair>::const_iterator itor = p_from_db.begin(); itor != p_from_db.end(); ++itor){
				stream << std::left << std::setw(max_reg)  << itor->reg_name << " ";
				stream << std::left << std::setw(max_val)  << itor->reg_val << " ";
				stream << std::left << std::setw(max_sol)  << itor->solution << " ";
				stream << std::left << std::setw(max_path) << itor->path << std::endl;

				stream << std::left << std::setw(max_reg)  << std::string(max_reg,'-') << " ";
				stream << std::left << std::setw(max_val)  << std::string(max_val, '-') << " ";
				stream << std::left << std::setw(max_sol)  << std::string(max_sol, '-') << " ";
				stream << std::left << std::setw(max_path) << std::string(max_path, '-') << std::endl;


			}

		} catch (std::runtime_error & msg){
			std::cerr<< msg.what() << std::endl;
		}
	}

	/**
	 * @brief Store the results of AllSAT to the database
	 *
	 */
	void store_to_database(){
		try{
			sqlite3 * db;
			if(sqlite3_open(p_database_path.c_str(), &db) != 0){
				std::string error_msg = "Could now open database: " + p_database_path;
				throw std::runtime_error(error_msg);
			}

			std::map<std::string, std::vector<std::vector<SingleResultPair> > >::const_iterator itor;
			std::vector<std::vector<SingleResultPair> >::const_iterator inner_itor;
			std::vector<SingleResultPair>::const_iterator sol_itor;
			for(itor = p_generated_results.begin(); itor != p_generated_results.end(); ++itor){
				int solution = 1;
				for(inner_itor = itor->second.begin(); inner_itor != itor->second.end(); ++inner_itor){
					for(sol_itor = inner_itor->begin(); sol_itor != inner_itor->end(); ++sol_itor){
						std::stringstream db_transaction;
						db_transaction << "insert into allsat values('"
								       << sol_itor->reg_name  << "','"
								       << sol_itor->reg_val   << "',"
									   << solution << ",'"
									   << itor->first
									   << "');";
						char * error_msg = 0;

						if (sqlite3_exec(db, db_transaction.str().c_str(), c_callback, 0 , &error_msg) != 0){
							std::string error_msg = "Can not executed query: " + db_transaction.str();
							throw std::runtime_error(error_msg);
						}
					}
					solution++;
				}
			}
			sqlite3_close(db);

		} catch (std::runtime_error & msg){
			std::cerr<< msg.what() << std::endl;
		}
	}

	/**
	 * @brief Set the path to the used database
	 *
	 * @param path The path to the database
	 */
	void set_database_path(std::string const & path){
		p_database_path = path;
	}

	/**
	 * @brief Get the currently used database path
	 *
	 * @return The path to the database
	 */
	std::string get_database_path() const {
		return p_database_path;
	}

	/**
	 * @param Callback forward function for the sqlite callback
	 *
	 * #FIXME: Make it a friend and not public!
	 */
	 int __callback__(int argc, char **argv, char **azColName){
		try {
			SingleResultPair tmp;
			for(int i = 0; i < argc; ++i){
				if (i == 0){
					tmp.reg_name = argv[i];
				} else if (i == 1){
					tmp.reg_val = argv[i];
				} else if (i == 2){
					tmp.solution = std::stoi(argv[i]);
				} else if (i == 3){
					tmp.path = argv[i];
				}
			}
			p_from_db.push_back(tmp);

		} catch (...){
			std::cerr<< "Unknown error caught!" << std::endl;
		}
		return 0;
		}

private:
	/**
	 *  @brief Disable CCTOR
	 */
	AllSAT (AllSAT const & sat);

	/**
	 * @brief Disable compare operator
	 */
	AllSAT operator= (AllSAT const & sat);

	/**
	 * @brief Representing a single solution value by Z3
	 */
	class SingleResultPair {
	public:
		std::string reg_name;
		std::string reg_val;
		int solution;
		std::string path;
	};

	/**
	 * @brief Representing a single smt2 file
	 */
	class FileStructure {
	public:
		std::string filename;
		std::vector<std::string> header;
		std::vector<std::string> variables;
		std::vector<std::string> assertions;
		std::vector<std::string> ending;

		/**
		 * @brief Dump smt2 structure to a stream
		 *
		 * @param stream The ostream to pipe the data to
		 */
		void dump(std::ostream & stream = std::cout) {
			stream << "Dumping " << this->filename << " ..." << std::endl;
			stream << "Header:" << std::endl;
			for (std::vector<std::string>::const_iterator itor = header.begin();
					itor != header.end(); ++itor) {
				stream << *itor << std::endl;
			}
			stream << "Variables:" << std::endl;
			for (std::vector<std::string>::const_iterator itor =
					variables.begin(); itor != variables.end(); ++itor) {
				stream << *itor << std::endl;
			}
			stream << "Assertions:" << std::endl;
			for (std::vector<std::string>::const_iterator itor =
					assertions.begin(); itor != assertions.end(); ++itor) {
				stream << *itor << std::endl;
			}
			stream << "Ending:" << std::endl;
			for (std::vector<std::string>::const_iterator itor = ending.begin();
					itor != ending.end(); ++itor) {
				stream << *itor << std::endl;
			}
		}
	};

	/**
	 * @brief Enumeration type for state machine based file reading
	 */
	enum FilePosition {
		header,
		variables,
		assertions,
		ending
	};

	std::string p_dir;
	std::vector<std::string> p_files;
	std::vector<FileStructure> p_filestructures;
	size_t p_execution_depth; // How many AllSAT solutions
	std::map<std::string, std::vector<std::vector<SingleResultPair> > > p_generated_results;
	std::string p_database_path;
	std::vector<SingleResultPair> p_from_db;

	/**
	 * @brief Read files from directory
	 */
	void read_directory(){
		try {
			boost::filesystem::path dir(p_dir);

			if (boost::filesystem::is_directory(p_dir)){
				boost::filesystem::directory_iterator itor(p_dir);
				boost::filesystem::directory_iterator end_itor;

				for(; itor != end_itor; ++itor){
					if (boost::filesystem::is_regular_file(itor->status())){
						p_files.push_back(itor->path().string());
					}
				}
			} else {
				std::string msg = p_dir + " is no valid directory!";
				throw new std::runtime_error(msg);
			}
		} catch (std::runtime_error & msg){
			std::cerr << msg.what() << std::endl;
		}
	}

	/**
	 * @brief Read smt2 file and store it in blocks variables/assertions/etc.
	 */
	void read_files(){
		std::string const start_variables = "; Start Variables";
		std::string const start_assertions = "; Start Assertions";
		std::string const start_ending = "; Start Ending";
		std::vector<std::string>::const_iterator itor, itor2;
		for(itor = p_files.begin(); itor != p_files.end(); ++itor){
			std::fstream ifile;
			ifile.open(*itor, std::ios::in);
			std::vector<std::string> file_content;
			std::string line;
			while(std::getline(ifile, line)){
				file_content.push_back(line);
			}
			ifile.close();

			FileStructure structure;
			FilePosition fpos = header;
			structure.filename = *itor;
			for(itor2 = file_content.begin(); itor2 != file_content.end(); ++itor2){

				if(fpos == header && itor2->find(start_variables) != std::string::npos){
					fpos = variables;
					continue;
				} else if (fpos == variables && itor2->find(start_assertions) != std::string::npos){
					fpos = assertions;
					continue;
				} else if (fpos == assertions && itor2->find(start_ending) != std::string::npos){
					fpos = ending;
				} else {
					switch(fpos){
					case header:
						structure.header.push_back(*itor2);
						break;
					case variables:
						structure.variables.push_back(*itor2);
						break;
					case assertions:
						structure.assertions.push_back(*itor2);
						break;
					case ending:
						structure.ending.push_back(*itor2);
						break;
					}
				}
			}
			p_filestructures.push_back(structure);
		}
	}

	/**
	 * @brief Execute AllSAT for a certain problem
	 *
	 * @param problem The AllSAT problem in form of a FileStructure instance
	 */
	void execute_allsat(FileStructure & problem){
#ifdef DEBUG
		std::cout << "Executing AllSAT for file: " << problem.filename << std::endl;
#endif
		size_t solutions = 0;
		bool sat = false;
		do {
			std::vector<std::string> result = solve_problem(problem);
			sat = is_sat(result.front());
			if(sat){
				std::vector<SingleResultPair> extracted_results = evaluate_results(result);
				p_generated_results[problem.filename].push_back(extracted_results);
				add_assertions(problem, extracted_results);

				solutions++;
			}
		} while(sat && solutions < p_execution_depth);
#ifdef DEBUG
		std::cout << "Found " << solutions << " SAT solutions for the problem" << std::endl;
#endif
	}

	/**
	 * @brief Add assertion to smt2 instance from last run to exclude those results from new result
	 *
	 * @param problem The formulated problem to be modified
	 * @param results The generated results to be used for assertion generation
	 */
	void add_assertions (FileStructure & problem, std::vector<SingleResultPair> const & results){
		std::stringstream sstream;
		sstream << "(assert (or ";
		for(std::vector<SingleResultPair>::const_iterator itor = results.begin(); itor != results.end(); ++itor){
			if(itor->reg_val == "true"){
				sstream << "(= " << itor->reg_name << " false )";
			} else {
				sstream << "(= " << itor->reg_name << " true)";
			}
		}
		sstream << "))";
		problem.assertions.push_back(sstream.str());
	}

	/**
	 * @brief Parse the first line of the result generated by z3 if result is sat
	 */
	bool is_sat(std::string const & line){
		if (line.find("unsat") != std::string::npos){
			return false;
		} else if (line.find("sat") != std::string::npos){
			return true;
		} else {
			return false;
		}
 	}

	/**
	 * @brief Write the formulate problem to disk and call Z3
	 *
	 * @param problem The smt instance to be executed
	 */
	std::vector<std::string> solve_problem(FileStructure const & problem){
		std::string tmp_file = "allsat.smt2";
		std::fstream outfile;
		outfile.open(p_dir + "/" + tmp_file, std::ios::out);
		std::vector<std::string>::const_iterator itor;
		for(itor = problem.header.begin(); itor != problem.header.end(); ++itor){
			outfile << *itor << std::endl;
		}
		for(itor = problem.variables.begin(); itor != problem.variables.end(); ++itor){
			outfile << *itor << std::endl;
		}
		for(itor = problem.assertions.begin(); itor != problem.assertions.end(); ++itor){
			outfile << *itor << std::endl;
		}
		for(itor = problem.ending.begin(); itor != problem.ending.end(); ++itor){
			outfile << *itor << std::endl;
		}
		outfile.close();

		std::string z3 = "z3";

		 boost::process::ipstream is; //reading pipe-stream
		 boost::process::child c(boost::process::search_path("z3"), p_dir + "/" + tmp_file, boost::process::std_out > is);

		 std::vector<std::string> result;
		 std::string line;

		 while (c.running() && std::getline(is, line) && !line.empty()){
			 result.push_back(line);
		  }

		  c.wait();
		  boost::filesystem::remove(p_dir + "/" + tmp_file);

		  return result;
	}

	/**
	 * @brief Extract the single values for every result line generated by Z3
	 *
	 * @param data The results generated by Z3 as string vector
	 * @return The values as SingleResultPair vector
	 */
	std::vector<SingleResultPair> evaluate_results (std::vector<std::string> const & data) {
		std::vector<std::string> sorted;
		std::vector<std::string>::const_iterator itor;
		std::string sort_what = "select_enable";
		std::vector<SingleResultPair> result_value;

		for(itor = data.begin(); itor != data.end(); ++itor){
			if(itor->find(sort_what) != std::string::npos){
				sorted.push_back(*itor);
			}
		}

		for(itor = sorted.begin(); itor != sorted.end(); ++itor){
			std::string tmp = itor->substr(2);
			tmp = tmp.substr(0, tmp.size()-2);
			std::stringstream sstr(tmp);
			std::string reg_name;
			std::string reg_val;
			sstr >> reg_name;
			sstr >> reg_val;

			SingleResultPair single_result;
			single_result.reg_name = reg_name;
			single_result.reg_val = reg_val;

			result_value.push_back(single_result);
		}

		return result_value;
	}

	/**
	 * @brief Static callback function for the sqlite3 api
	 * This static function gets the this pointer of the class and forwards the
	 * data to an actual member of the class to have access to the memory
	 */
	 static int c_callback(void *data, int argc, char **argv, char **azColName){
		 AllSAT * tmp = reinterpret_cast<AllSAT*>(data);
		 return tmp->__callback__(argc, argv, azColName);
	 }
};

#endif /* ALLSAT_HPP_ */
