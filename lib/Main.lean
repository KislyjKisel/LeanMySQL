/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import MySql

open MySql

def main : IO Unit := do
  let mysql ← MySql.mk
  IO.println version
  mysql.login "localhost" "root" "root"
  mysql.createDB "test_db"
  mysql.useDB "test_db"

  mysql.createTable "job" [
    ("id", "INT PRIMARY KEY"),
    ("job_name", "VARCHAR(255)")
  ]
  mysql.insertIntoTable "job" [1, "Computer Scientist"]
  mysql.insertIntoTable "job" [2, "Mathematician"]

  mysql.createTable "person" [
      ("id", "SERIAL PRIMARY KEY"),
      ("name", "VARCHAR(255)"),
      ("age", "INT"),
      ("height", "FLOAT"),
      ("job_id", "INT"),
      ("country_id", "INT")
    ]
  mysql.insertIntoTable "person" [.default, "Alice", 20, 1.72, 1, 1]
  mysql.insertIntoTable "person" [.default, "Bob", 21, 1.64, 2, 3]
  mysql.insertIntoTable "person" [.default, "Craig", 22, 1.76, .null, 2]

  let df ← mysql.query $
    SELECT name, age, height, job_name
    FROM person LEFT JOIN job ON person.job_id = job.id
    WHERE person.age > 20

  IO.println $ df

  mysql.close
