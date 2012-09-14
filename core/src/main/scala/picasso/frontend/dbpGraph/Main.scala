package picasso.frontend.dbpGraph

import picasso.frontend.Runner

object Main extends Runner {

  type P = DBPGraphs.DBCGraph
  def parse = DBPGraphParser.apply

}
