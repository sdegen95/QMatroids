using SQLite
using Tables
include("./q_matroids.jl")


##############################################################################################################
# Creation of the database and the table inside (comment out this section after you first complied)
##############################################################################################################

# # Create a database for q-matroids
# db = SQLite.DB("New_QMatroids_for_Oscar/q_matroids_db")

# # Create the table
# TABLE_NAME = "q_Matroids"
# NAMES = ["Encoding",
#          "Char",
#          "Dim",
#          "Rank",
#          "Loopspace_dim",
#          "Is_reprenstable",
#          "Base_spaces",
#          "Independent_spaces",
#          "Dependent_spaces",
#          "Circuits",
#          "Open_spaces",
#          "Flats",
#          "Hyperplanes",
#          "Cyclic_flats",
#          "Spanning_spaces",
#          "Characteristic_poly",
#          "Aut_group",
#          "Is_paving",
#          "Is_full",
#          "Is_irreducible"]
# TYPES = [String for i in range(1,length(NAMES))]
# SCHEMA = Tables.Schema(NAMES, TYPES)
# SQLite.createtable!(db, TABLE_NAME, SCHEMA, temp=false, ifnotexists=true)
#SQLite.createindex!(db, TABLE_NAME, "ID", "ID", unique=true, ifnotexists=true)


##############################################################################################################
# Functionality 
##############################################################################################################


@doc raw"""
    Add_entry(QM::Q_Matroid, db:: SQLite.DB, con::Module, table_name::String)

    This function will create an entry, with values specified above, for the given q_matroid in the table `q_Matroids` in a database `db` containing such a table.   
"""

function Add_entry(QM::Q_Matroid, db:: SQLite.DB, con::Module, table_name="q_Matroids"::String)
    Field = base_ring(QM.groundspace)
    Char = Int(characteristic(Field))
    Dim = ncols(QM.groundspace)
    Bases = QM.bases
    q_Rank = rank(Bases[1])
    Indeps = Q_Matroid_Indepentspaces(QM)
    Deps = Q_Matroid_Depentspaces(QM)
    all_sp = subspaces_fix_dim(Field,q_Rank,Dim)

    # Helper for removing ugly string notation in the entry
    re = r"fpMatrix"

    # Compute all 20 values for the table
    N_Bases = replace("$(QM.bases)",re=>"")
    N_Indeps = replace("$(Q_Matroid_Indepentspaces(QM))",re=>"")
    N_Deps = replace("$(Q_Matroid_Depentspaces(QM))",re=>"")
    Encoding = join(binary_encoding(Bases,all_sp))*"_r$(q_Rank)d$(Dim)"
    Loopspace_dim = rank(vcat(Q_Matroid_Loopspace(QM)))
    Is_repable = Is_representable(QM)
    Circuits = replace("$(Q_Matroid_Circuits(QM))",re=>"")
    Open_spaces = replace("$(Q_Matroid_Openspaces(QM))",re=>"")
    Flats = replace("$(Q_Matroid_Flats(QM))",re=>"")
    Hyperplanes = replace("$(Q_Matroid_Hyperplanes(QM))",re=>"")
    Cyclic_flats = replace("$(Q_Matroid_CyclicFlats(QM))",re=>"")
    Spanning_spaces = replace("$(Q_Matroid_Spanningspaces(QM))",re=>"")
    Characteristic_poly = Q_Matroid_charpoly(QM,Indeps,Deps)
    Aut_group = Oscar.describe(Q_Matroid_Aut(QM))
    Is_paving = Is_paving_q_matroid(QM)
    Is_full = Is_full_q_matroid(QM)

    # Currently not computable
    Is_irreducible = "missing"

    # Add the entry to the choosen table
    return con.execute(db, "INSERT INTO $(table_name) VALUES(   '$(Encoding)',
                                                                '$(Char)',
                                                                '$(Dim)',
                                                                '$(q_Rank)',
                                                                '$(Loopspace_dim)',
                                                                '$(Is_repable)',
                                                                '$(N_Bases)',
                                                                '$(N_Indeps)',
                                                                '$(N_Deps)',
                                                                '$(Circuits)',
                                                                '$(Open_spaces)',
                                                                '$(Flats)',
                                                                '$(Hyperplanes)',
                                                                '$(Cyclic_flats)',
                                                                '$(Spanning_spaces)',
                                                                '$(Characteristic_poly)',
                                                                '$(Aut_group)',
                                                                '$(Is_paving)',
                                                                '$(Is_full)',
                                                                '$(Is_irreducible)')")

end
##############################################################################################################