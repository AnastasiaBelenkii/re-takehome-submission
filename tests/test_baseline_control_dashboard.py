from scripts.run_baseline_control_wave import dashboard


def test_dashboard_uses_run_timestamp_for_eta(monkeypatch) -> None:
    monkeypatch.setattr("scripts.run_baseline_control_wave.time.time", lambda: 1000.0)
    monkeypatch.setattr("scripts.run_baseline_control_wave.datetime", __import__("datetime").datetime)
    jobs = {}
    run_ids = (
        "qwen-stock-25-r2", "gpt-stock-25-r2", "portfolio-25x2-r2",
        "qwen-stock-50-r1", "qwen-stock-50-r2", "gpt-stock-50-r1", "gpt-stock-50-r2",
    )
    for index, run_id in enumerate(run_ids):
        jobs[run_id] = {
            "host": f"worker-{index}",
            "run_root": f"/runs/{run_id}-19700101T001000.000000Z-deadbeef",
            "launched_epoch": 999.0,
            "last_poll": {"state": "running", "completed": 4, "score": None},
        }
    rendered = dashboard({"updated_at": "now", "jobs": jobs}, [])
    assert "ETA ~20m" in rendered
    assert "ETA ~0m" not in rendered
