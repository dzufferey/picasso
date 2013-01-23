package picasso.frontend.dbpGraph

import picasso.frontend.Runner

object Main extends Runner[DBPGraphs.DBCGraph] {

  def parse(input: String) = DBPGraphParser.apply(input)

}
